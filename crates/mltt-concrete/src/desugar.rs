use crate::syntax::{concrete, raw};

pub fn desugar_module(items: &[concrete::Item]) -> Vec<raw::Item> {
    items.iter().map(desugar_item).collect()
}

pub fn desugar_item(item: &concrete::Item) -> raw::Item {
    match item {
        concrete::Item::Declaration { docs, name, ann } => raw::Item::Declaration {
            docs: docs.clone(),
            name: name.clone(),
            ann: desugar_term(ann),
        },
        concrete::Item::Definition {
            docs,
            name,
            param_names,
            body_ty,
            body,
        } => raw::Item::Definition {
            docs: docs.clone(),
            name: name.clone(),
            body: {
                let body = match body_ty {
                    Some(body_ty) => {
                        let body_ty = desugar_term(body_ty);
                        let body = desugar_term(body);
                        raw::RcTerm::from(raw::Term::Ann(body, body_ty))
                    },
                    None => desugar_term(body),
                };

                raw::RcTerm::from(raw::Term::FunIntro(param_names.clone(), body))
            },
        },
    }
}

pub fn desugar_term(term: &concrete::Term) -> raw::RcTerm {
    match term {
        concrete::Term::Var(name) => raw::RcTerm::from(raw::Term::Var(name.clone())),
        concrete::Term::Literal(literal) => raw::RcTerm::from(raw::Term::Literal(literal.clone())),
        concrete::Term::Let(name, def, body) => {
            let def = desugar_term(def);
            let body = desugar_term(body);

            raw::RcTerm::from(raw::Term::Let(name.clone(), def, body))
        },
        concrete::Term::Ann(term, ann) => {
            let term = desugar_term(term);
            let ann = desugar_term(ann);

            raw::RcTerm::from(raw::Term::Ann(term, ann))
        },
        concrete::Term::Parens(term) => raw::RcTerm::from(raw::Term::Parens(desugar_term(term))),

        // Functions
        concrete::Term::FunType(params, body_ty) => raw::RcTerm::from(raw::Term::FunType(
            params
                .iter()
                .map(|(param_names, param_ty)| (param_names.clone(), desugar_term(param_ty)))
                .collect(),
            desugar_term(body_ty),
        )),
        concrete::Term::FunArrowType(param_ty, body_ty) => {
            let param_ty = desugar_term(param_ty);
            let body_ty = desugar_term(body_ty);

            raw::RcTerm::from(raw::Term::FunArrowType(param_ty, body_ty))
        },
        concrete::Term::FunIntro(param_names, body) => {
            raw::RcTerm::from(raw::Term::FunIntro(param_names.clone(), desugar_term(body)))
        },
        concrete::Term::FunApp(fun, args) => raw::RcTerm::from(raw::Term::FunApp(
            desugar_term(fun),
            args.iter().map(desugar_term).collect(),
        )),

        // Pairs
        concrete::Term::PairType(name, fst_ty, snd_ty) => {
            let fst_ty = desugar_term(fst_ty);
            let snd_ty = desugar_term(snd_ty);

            raw::RcTerm::from(raw::Term::PairType(name.clone(), fst_ty, snd_ty))
        },
        concrete::Term::PairIntro(fst, snd) => {
            let fst = desugar_term(fst);
            let snd = desugar_term(snd);

            raw::RcTerm::from(raw::Term::PairIntro(fst, snd))
        },
        concrete::Term::PairFst(pair) => {
            let pair = desugar_term(pair);

            raw::RcTerm::from(raw::Term::PairFst(pair))
        },
        concrete::Term::PairSnd(pair) => {
            let pair = desugar_term(pair);

            raw::RcTerm::from(raw::Term::PairSnd(pair))
        },

        // Universes
        concrete::Term::Universe(level) => raw::RcTerm::from(raw::Term::Universe(*level)),
    }
}
