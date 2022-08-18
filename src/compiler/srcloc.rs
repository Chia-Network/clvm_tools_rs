use std::fmt::Display;
use std::rc::Rc;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Srcloc {
    pub file: Rc<String>,
    pub line: usize,
    pub col: usize,
    pub until: Option<(usize, usize)>,
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
        match self.until {
            None => formatter.write_str(&format!("{}({}):{}", self.file, self.line, self.col)),
            Some((l, c)) => formatter.write_str(&format!(
                "{}({}):{}-{}({}):{}",
                self.file, self.line, self.col, self.file, l, c
            )),
        }
    }
}

impl Srcloc {
    pub fn ext(&self, other: &Srcloc) -> Srcloc {
        combine_src_location(self, other)
    }

    pub fn advance(&self, ch: u8) -> Srcloc {
        match ch as char {
            '\n' => Srcloc {
                file: self.file.clone(),
                col: 1,
                line: self.line + 1,
                until: self.until,
            },
            '\t' => {
                let next_tab = (self.col + 8) & !7;
                Srcloc {
                    file: self.file.clone(),
                    col: next_tab,
                    line: self.line,
                    until: self.until,
                }
            }
            _ => Srcloc {
                file: self.file.clone(),
                col: self.col + 1,
                line: self.line,
                until: self.until,
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
    match a.until {
        None => (a.line, a.col + 1),
        Some((ll, cc)) => (ll, cc),
    }
}

fn add_onto(x: &Srcloc, y: &Srcloc) -> Srcloc {
    Srcloc {
        file: x.file.clone(),
        line: x.line,
        col: x.col,
        until: Some(src_location_max(y)),
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
