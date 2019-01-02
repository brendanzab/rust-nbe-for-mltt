use mltt_core::syntax::UniverseLevel;

use crate::syntax::{concrete, raw};

pub fn desugar(term: &concrete::Term) -> raw::RcTerm {
    match *term {
        concrete::Term::Var(ref ident) => raw::RcTerm::from(raw::Term::Var(ident.clone())),
        concrete::Term::Let(ref ident, ref def, ref body) => {
            let def = desugar(def);
            let body = desugar(body);

            raw::RcTerm::from(raw::Term::Let(ident.clone(), def, body))
        },
        concrete::Term::Ann(ref term, ref ann) => {
            let term = desugar(term);
            let ann = desugar(ann);

            raw::RcTerm::from(raw::Term::Ann(term, ann))
        },
        concrete::Term::Parens(ref term) => desugar(term),

        // Functions
        concrete::Term::FunType(ref ident, ref param_ty, ref body_ty) => {
            let param_ty = desugar(param_ty);
            let body_ty = desugar(body_ty);

            raw::RcTerm::from(raw::Term::FunType(ident.clone(), param_ty, body_ty))
        },
        concrete::Term::FunIntro(ref ident, ref body) => {
            let body = desugar(body);

            raw::RcTerm::from(raw::Term::FunIntro(ident.clone(), body))
        },
        concrete::Term::FunApp(ref fun, ref args) => args.iter().fold(desugar(fun), |acc, arg| {
            let arg = desugar(arg);
            raw::RcTerm::from(raw::Term::FunApp(acc, arg))
        }),

        // Pairs
        concrete::Term::PairType(ref ident, ref fst_ty, ref snd_ty) => {
            let fst_ty = desugar(fst_ty);
            let snd_ty = desugar(snd_ty);

            raw::RcTerm::from(raw::Term::PairType(ident.clone(), fst_ty, snd_ty))
        },
        concrete::Term::PairIntro(ref fst, ref snd) => {
            let fst = desugar(fst);
            let snd = desugar(snd);

            raw::RcTerm::from(raw::Term::PairIntro(fst, snd))
        },
        concrete::Term::PairFst(ref pair) => {
            let pair = desugar(pair);

            raw::RcTerm::from(raw::Term::PairFst(pair))
        },
        concrete::Term::PairSnd(ref pair) => {
            let pair = desugar(pair);

            raw::RcTerm::from(raw::Term::PairSnd(pair))
        },

        // Universes
        concrete::Term::Universe(level) => match level {
            None => raw::RcTerm::from(raw::Term::Universe(UniverseLevel(0))),
            Some(level) => raw::RcTerm::from(raw::Term::Universe(UniverseLevel(level))),
        },
    }
}
