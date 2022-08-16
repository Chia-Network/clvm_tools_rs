use std::fs;

pub fn newer(input_path: &str, output_path: &str) -> Result<bool, String> {
    if !std::path::Path::new(output_path).exists() {
        return Ok(true);
    }

    fs::metadata(input_path)
        .map_err(|_| "source does not exist".to_string())
        .and_then(|im| {
            fs::metadata(output_path)
                .map(|om| im.modified().unwrap() >= om.modified().unwrap())
                .map_err(|_| "could not stat dest".to_string())
        })
}
