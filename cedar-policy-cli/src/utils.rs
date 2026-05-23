/*
 * Copyright Cedar Contributors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use miette::{IntoDiagnostic, Result, WrapErr};
use std::path::Path;

mod policies;
pub use policies::*;
mod links;
pub(crate) use links::*;
mod request;
pub use request::*;
mod schema;
pub use schema::*;
mod entities;
pub(crate) use entities::*;

// Read from a file (when `filename` is a `Some`) or stdin (when `filename` is `None`) to a `String`
pub(crate) fn read_from_file_or_stdin(
    filename: Option<&impl AsRef<Path>>,
    context: &str,
) -> Result<String> {
    let mut src_str = String::new();
    match filename {
        Some(path) => {
            src_str = std::fs::read_to_string(path)
                .into_diagnostic()
                .wrap_err_with(|| {
                    format!("failed to open {context} file {}", path.as_ref().display())
                })?;
        }
        None => {
            std::io::Read::read_to_string(&mut std::io::stdin(), &mut src_str)
                .into_diagnostic()
                .wrap_err_with(|| format!("failed to read {context} from stdin"))?;
        }
    };
    Ok(src_str)
}

const POLTREE_CACHE_VERSION: u32 = 1;

fn policy_format_tag(policy_format: PolicyFormat) -> u8 {
    match policy_format {
        PolicyFormat::Cedar => 1,
        PolicyFormat::Json => 2,
    }
}

fn hash_file(path: &Path) -> Result<u64> {
    use std::io::Read;
    let mut file = std::fs::File::open(path)
        .into_diagnostic()
        .wrap_err_with(|| format!("failed to open file {} for hashing", path.display()))?;
    let mut hasher = xxhash_rust::xxh3::Xxh3::new();
    let mut buf = [0_u8; 64 * 1024];
    loop {
        let read = file
            .read(&mut buf)
            .into_diagnostic()
            .wrap_err_with(|| format!("failed to read file {} while hashing", path.display()))?;
        if read == 0 {
            break;
        }
        hasher.update(&buf[..read]);
    }
    Ok(hasher.digest())
}

fn hash_file_if_exists(path: &Path) -> Result<u64> {
    if path.exists() {
        hash_file(path)
    } else {
        Ok(0)
    }
}

pub(crate) fn poltree_cache_path(
    policies: &PoliciesArgs,
    entities_filename: &Path,
    schema_file: Option<&Path>,
) -> Result<Option<std::path::PathBuf>> {
    let Some(policy_file) = policies.policies_file.as_ref() else {
        return Ok(None);
    };

    let policy_hash = hash_file(Path::new(policy_file))?;
    let entities_hash = hash_file(entities_filename)?;
    let schema_hash = match schema_file {
        Some(path) => hash_file(path)?,
        None => 0,
    };
    let template_hash = match policies.template_linked_file.as_ref() {
        Some(path) => hash_file_if_exists(Path::new(path))?,
        None => 0,
    };

    let policy_format = policy_format_tag(policies.policy_format);

    let cache_dir = std::env::current_dir()
        .into_diagnostic()
        .wrap_err("failed to resolve current directory")?
        .join("target")
        .join(".cedar")
        .join("poltree-cache");
    std::fs::create_dir_all(&cache_dir)
        .into_diagnostic()
        .wrap_err_with(|| format!("failed to create cache directory {}", cache_dir.display()))?;

    let file_name = format!(
        "v{POLTREE_CACHE_VERSION}_pf{policy_format}_{policy_hash:016x}_{entities_hash:016x}_{schema_hash:016x}_{template_hash:016x}.bin"
    );
    Ok(Some(cache_dir.join(file_name)))
}

// Convenient wrapper around `read_from_file_or_stdin` to just read from a file
fn read_from_file(filename: impl AsRef<Path>, context: &str) -> Result<String> {
    read_from_file_or_stdin(Some(&filename), context)
}

#[cfg(test)]
pub(crate) mod test_utils {
    /// Insta filter to replace non-deterministic temp file paths.
    pub const TEMPFILE_FILTER: (&str, &str) = (r"/tmp/\.tmp[A-Za-z0-9]+", "<TEMPFILE>");

    /// Render a miette Report as unicode text without ANSI color codes.  ANSI
    /// codes cause inconsistent snapshots depending whether miette decides the
    /// environment supports colors.
    pub fn render_err(err: &miette::Report) -> String {
        let mut buf = String::new();
        miette::GraphicalReportHandler::new_themed(miette::GraphicalTheme::unicode_nocolor())
            .render_report(&mut buf, err.as_ref())
            .unwrap();
        buf
    }
}
