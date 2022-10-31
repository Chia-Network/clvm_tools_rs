use std::borrow::Borrow;
use std::fmt::Display;
use std::rc::Rc;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Until {
    pub line: usize,
    pub col: usize,
}

impl Until {
    pub fn from_pair(p: (usize, usize)) -> Self {
        Until {
            line: p.0,
            col: p.1,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Srcloc {
    pub file: Rc<String>,
    pub line: usize,
    pub col: usize,
    pub until: Option<Until>,
}

// let srcLocationToJson sl =
//   let b =
//     [ ("line", Js.Json.number (float_of_int sl.line))
//     ; ("col", Js.Json.number (float_of_int sl.col))
//     ]
//   in
//   let u =
//     match sl.until with
//     | None -> []
//     | Some (l,c) ->
//       [ ("ml", Js.Json.number (float_of_int l))
//       ; ("mc", Js.Json.number (float_of_int c))
//       ]
//   in
//   List.concat [ b ; u ]
//   |> Js.Dict.fromList
//   |> Js.Json.object_

impl Display for Srcloc {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match &self.until {
            None => formatter.write_str(&format!("{}({}):{}", self.file, self.line, self.col)),
            Some(u) => formatter.write_str(&format!(
                "{}({}):{}-{}({}):{}",
                self.file, self.line, self.col, self.file, u.line, u.col
            )),
        }
    }
}

impl Srcloc {
    pub fn new(name: Rc<String>, line: usize, col: usize) -> Self {
        Srcloc {
            file: name,
            line,
            col,
            until: None,
        }
    }

    pub fn ending(&self) -> Srcloc {
        if let Some(u) = &self.until {
            return Srcloc {
                file: self.file.clone(),
                line: u.line,
                col: u.col,
                until: None,
            };
        }
        self.clone()
    }

    pub fn overlap(&self, other: &Srcloc) -> bool {
        let mf: &String = self.file.borrow();
        let of: &String = other.file.borrow();
        if mf != of {
            return false;
        }

        if self.line == other.line && self.col == other.col {
            return true;
        }

        match (self.until.as_ref(), other.until.as_ref()) {
            (None, None) => self.line == other.line && self.col == other.col,
            (None, Some(_)) => other.overlap(self),
            (Some(self_until), None) => {
                if self.line < other.line && self_until.line > other.line {
                    return true;
                }
                // The case where we have len means we have only one line in the self srcloc.
                // In that case, we want to encompass other with our range (since it's singular).
                if let Some(len) = self.len() {
                    if self.line == other.line
                        && self.col <= other.col
                        && self.col + len >= other.col
                    {
                        return true;
                    }
                } else {
                    // In this case, we have match if other is on the same line as self and after
                    // self.col or on the same line as self_until and before col.
                    if self.line == other.line && self.col <= other.col
                        || self_until.line == other.line && self_until.col >= other.col
                    {
                        return true;
                    }
                }

                false
            }
            (Some(my_until), Some(their_until)) => {
                let self_start = Srcloc::new(self.file.clone(), self.line, self.col);
                let self_until = Srcloc::new(self.file.clone(), my_until.line, my_until.col);
                let other_start = Srcloc::new(self.file.clone(), other.line, other.col);
                let other_until = Srcloc::new(self.file.clone(), their_until.line, their_until.col);
                other.overlap(&self_start)
                    || other.overlap(&self_until)
                    || self.overlap(&other_start)
                    || self.overlap(&other_until)
            }
        }
    }

    pub fn is_empty(&self) -> bool {
        false
    }

    // Length of the string representation for the srcloc's range if it's on
    // the same line.  Some thought is needed to know what we want for a range
    // over lines.
    pub fn len(&self) -> Option<usize> {
        if let Some(self_until) = &self.until {
            if self_until.line != self.line {
                None
            } else {
                Some(self_until.col - self.col)
            }
        } else {
            Some(1)
        }
    }

    pub fn ext(&self, other: &Srcloc) -> Srcloc {
        if other.file == self.file {
            combine_src_location(self, other)
        } else {
            self.clone()
        }
    }

    pub fn advance(&self, ch: u8) -> Srcloc {
        match ch as char {
            '\n' => Srcloc {
                file: self.file.clone(),
                col: 1,
                line: self.line + 1,
                until: self.until.clone(),
            },
            '\t' => {
                let next_tab = (self.col + 8) & !7;
                Srcloc {
                    file: self.file.clone(),
                    col: next_tab,
                    line: self.line,
                    until: self.until.clone(),
                }
            }
            _ => Srcloc {
                file: self.file.clone(),
                col: self.col + 1,
                line: self.line,
                until: self.until.clone(),
            },
        }
    }

    pub fn start(file: &str) -> Srcloc {
        Srcloc {
            file: Rc::new(file.to_string()),
            line: 1,
            col: 1,
            until: None,
        }
    }
}

pub fn src_location_min(a: &Srcloc) -> (usize, usize) {
    (a.line, a.col)
}

pub fn src_location_max(a: &Srcloc) -> (usize, usize) {
    match &a.until {
        None => (a.line, a.col + 1),
        Some(u) => (u.line, u.col),
    }
}

fn add_onto(x: &Srcloc, y: &Srcloc) -> Srcloc {
    Srcloc {
        file: x.file.clone(),
        line: x.line,
        col: x.col,
        until: Some(Until::from_pair(src_location_max(y))),
    }
}

pub fn combine_src_location(a: &Srcloc, b: &Srcloc) -> Srcloc {
    match (a.line < b.line, a.line == b.line) {
        (true, _) => add_onto(a, b),
        (_, true) => match (a.col < b.col, a.col == b.col) {
            (true, _) => add_onto(a, b),
            (_, true) => a.clone(),
            _ => add_onto(b, a),
        },
        _ => add_onto(b, a),
    }
}
