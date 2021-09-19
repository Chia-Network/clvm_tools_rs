use std::rc::Rc;
use std::string::String;

use crate::compiler::srcloc::Srcloc;
use crate::util::Number;

// Compiler view of SExp
pub enum SExp {
    Nil(Srcloc),
    Cons(Srcloc,Rc<SExp>,Rc<SExp>),
    Integer(Srcloc,Number),
    QuotedString(Srcloc,u8,Vec<u8>),
    Atom(Srcloc, Vec<u8>)
}

impl SExp {
    pub fn loc(&self) -> Srcloc {
        match self {
            SExp::Nil(l) => l.clone(),
            SExp::Cons(l,_,_) => l.clone(),
            SExp::Integer(l,_) => l.clone(),
            SExp::QuotedString(l,_,_) => l.clone(),
            SExp::Atom(l,_) => l.clone()
        }
    }

    pub fn atom_from_string(loc: Srcloc, s: &String) -> SExp {
        return SExp::Atom(loc, s.as_bytes().to_vec());
    }

    pub fn quoted_from_string(loc: Srcloc, s: &String) -> SExp {
        return SExp::QuotedString(loc, '\"' as u8, s.as_bytes().to_vec());
    }
}
