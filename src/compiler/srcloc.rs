#[derive(Clone)]
pub struct Srcloc {
    file: String,
    line: usize,
    col: usize,
    until: Option<(usize, usize)>
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

impl Srcloc {
    fn to_string(&self) -> String {
        match self.until {
            None => format!("{}({}):{}", self.file, self.line, self.col),
            Some((l,c)) => format!("{}({}):{}-{}({}):{}", self.file, self.line, self.col, self.file, l, c)
        }
    }
}

pub fn src_location_min(a: &Srcloc) -> (usize, usize) {
    return (a.line, a.col);
}

pub fn src_location_max(a: &Srcloc) -> (usize, usize) {
    match a.until {
        None => (a.line, a.col + 1),
        Some((ll,cc)) => (ll,cc)
    }
}

fn add_onto(x: &Srcloc, y: &Srcloc) -> Srcloc {
    Srcloc {
        file: x.file.to_string(),
        line: x.line,
        col: x.col,
        until: Some(src_location_max(y))
    }
}

pub fn combine_src_location(a: &Srcloc, b: &Srcloc) -> Srcloc {
    if a.line < b.line {
        add_onto(a, b)
    } else if a.line == b.line {
        if a.col < b.col {
            add_onto(a, b)
        } else if a.col == b.col {
            a.clone()
        } else {
            add_onto(b, a)
        }
    } else {
        add_onto(b, a)
    }
}

pub fn start(file: String) -> Srcloc {
    Srcloc {
        file: file.to_string(),
        line: 1,
        col: 1,
        until: None
    }
}

pub fn advance(loc: &Srcloc, ch: char) -> Srcloc {
    match ch {
        '\n' =>
            Srcloc {
                file: loc.file.to_string(),
                col: 1,
                line: loc.line + 1,
                until: loc.until
            },
        '\t' => {
            let next_tab = (loc.col + 8) & !7;
            Srcloc {
                file: loc.file.to_string(),
                col: next_tab,
                line: loc.line,
                until: loc.until
            }
        }
    }
}
