use std::string::String;

// Compiler view of SExp
pub enum SExp<Loc> {
    Nil(Loc),
    Cons(Loc,Box<SExp<Loc>>,Box<SExp<Loc>>),
    Integer(Loc,String),
    QuotedString(Loc,u8,String)
}
