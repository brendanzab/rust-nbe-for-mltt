use mltt_core::syntax::UniverseLevel;

use crate::syntax::{concrete, raw};

pub fn desugar_term(term: &concrete::Term) -> raw::RcTerm {
    match *term {
        concrete::Term::Var(ref name) => raw::RcTerm::from(raw::Term::Var(name.clone())),
        concrete::Term::Let(ref name, ref def, ref body) => {
            let def = desugar_term(def);
            let body = desugar_term(body);

            raw::RcTerm::from(raw::Term::Let(name.clone(), def, body))
        },
        concrete::Term::Ann(ref term, ref ann) => {
            let term = desugar_term(term);
            let ann = desugar_term(ann);

            raw::RcTerm::from(raw::Term::Ann(term, ann))
        },
        concrete::Term::Parens(ref term) => desugar_term(term),

        // Functions
        concrete::Term::FunType(ref name, ref param_ty, ref body_ty) => {
            let param_ty = desugar_term(param_ty);
            let body_ty = desugar_term(body_ty);

            raw::RcTerm::from(raw::Term::FunType(Some(name.clone()), param_ty, body_ty))
        },
        concrete::Term::FunArrowType(ref param_ty, ref body_ty) => {
            let param_ty = desugar_term(param_ty);
            let body_ty = desugar_term(body_ty);

            raw::RcTerm::from(raw::Term::FunType(None, param_ty, body_ty))
        },
        concrete::Term::FunIntro(ref name, ref body) => {
            let body = desugar_term(body);

            raw::RcTerm::from(raw::Term::FunIntro(name.clone(), body))
        },
        concrete::Term::FunApp(ref fun, ref args) => {
            args.iter().fold(desugar_term(fun), |acc, arg| {
                let arg = desugar_term(arg);
                raw::RcTerm::from(raw::Term::FunApp(acc, arg))
            })
        },

        // Pairs
        concrete::Term::PairType(ref name, ref fst_ty, ref snd_ty) => {
            let fst_ty = desugar_term(fst_ty);
            let snd_ty = desugar_term(snd_ty);

            raw::RcTerm::from(raw::Term::PairType(name.clone(), fst_ty, snd_ty))
        },
        concrete::Term::PairIntro(ref fst, ref snd) => {
            let fst = desugar_term(fst);
            let snd = desugar_term(snd);

            raw::RcTerm::from(raw::Term::PairIntro(fst, snd))
        },
        concrete::Term::PairFst(ref pair) => {
            let pair = desugar_term(pair);

            raw::RcTerm::from(raw::Term::PairFst(pair))
        },
        concrete::Term::PairSnd(ref pair) => {
            let pair = desugar_term(pair);

            raw::RcTerm::from(raw::Term::PairSnd(pair))
        },

        // Universes
        concrete::Term::Universe(level) => match level {
            None => raw::RcTerm::from(raw::Term::Universe(UniverseLevel(0))),
            Some(level) => raw::RcTerm::from(raw::Term::Universe(UniverseLevel(level))),
        },
    }
}
