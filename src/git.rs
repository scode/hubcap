use failure::Error;
//use regex::Regex;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;

/// The possible states a file can be in, as reported by `git status`.
///
/// See git-status(1).
pub enum FileStatus {
    Modified(PathBuf),
    Added(PathBuf),
    Deleted(PathBuf),
    Renamed { new: PathBuf, old: PathBuf },
    Copied { new: PathBuf, old: PathBuf },
    UpdatedUnMerged(PathBuf),
}

pub trait Git {
    /// Inspect the status of the working copy and return a description of it.
    ///
    /// This is the equivalent of `git status`.
    ///
    /// If the git working copy is clean, an empty vec is returned.
    fn status(&self) -> Result<Vec<FileStatus>, Error>;
}

/// An implementation of the Git trait which uses a git binary present on the system to interact
/// with a git repository.
pub struct SystemGit {
    /// The path of the git binary to execute.
    git_path: PathBuf,

    /// The path to the git repository; equivalent of the -C argument to git.
    repo_path: PathBuf,
}

impl SystemGit {
    /// Create a SystemGit with default configuration
    ///
    /// See the various public builder methods that alter the configuration for their corresponding
    /// default values.
    pub fn new() -> SystemGit {
        SystemGit {
            git_path: PathBuf::from("git"),
            repo_path: PathBuf::from("."),
        }
    }

    /// Set the path to the git binary to use. By default, the path is `git` and it is assumed to
    /// be present in `PATH`.
    pub fn git_path<'a>(&'a mut self, path: &Path) -> &'a mut SystemGit {
        self.git_path = PathBuf::from(path);
        self
    }

    /// Set the path to the repo on which to operate. By default, the path is `.`.
    ///
    /// This is the equivalent of the `-C` argument to git.
    pub fn repo_path<'a>(&'a mut self, path: &Path) -> &'a mut SystemGit {
        self.repo_path = PathBuf::from(path);
        self
    }

    fn git_command(&self) -> Result<Command, Error> {
        let git_path_str = path_to_str(&self.git_path)?;
        let repo_path_str = path_to_str(&self.repo_path)?;

        let mut cmd = Command::new(git_path_str);
        cmd.arg("-C").arg(repo_path_str);

        Ok(cmd)
    }
}

impl Git for SystemGit {
    fn status(&self) -> Result<Vec<FileStatus>, Error> {
        let mut cmd = self.git_command()?;

        cmd.arg("status").arg("-z");

        let output = cmd.output()?;

        if !output.status.success() {
            return Err(format_err!(
                "git terminated in error: {}",
                String::from_utf8(output.stderr)?
            ));
        }

        let stdout = String::from_utf8(output.stdout)?;

        // See gitb-status(1) for the behavior of -z. But in short:
        //
        //    <STATUS FLAG OR SPACE> <STATUS FLAG> <SPACE> <ANY CHARACTER EXCEPT NUL REPEATED> NUL
        let status_lines: Vec<&str> = stdout.split('\0').collect();
        let statuses: Vec<&str> = status_lines.iter().map(|line| *line).collect();
        //let q = status_lines.chars().take(2);
        //let re = Regex::new("test").unwrap();

        Ok(vec![])
    }
}

/// Convert a Path to a String, failing with an error if the string is not valid utf-8.
///
/// Future: Use https://doc.rust-lang.org/std/option/struct.NoneError.html when stable?
fn path_to_str(p: &Path) -> Result<String, Error> {
    p.to_str()
        .ok_or_else(|| format_err!("path is not valid utf-8: {:?}", p))
        .map(|s| s.to_owned())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn path_to_str_valid_utf8() {
        assert_eq!(
            path_to_str(&PathBuf::from("valid utf-8")).unwrap(),
            "valid utf-8"
        );
    }

    #[test]
    fn path_to_str_invalid_utf8() {
        use std::ffi::OsStr;
        use std::os::unix::ffi::OsStrExt;

        let bytes: &[u8] = &vec![255u8];
        let osstr = OsStr::from_bytes(bytes);
        let pb = PathBuf::from(osstr);

        assert!(path_to_str(&pb).is_err())
    }
}
