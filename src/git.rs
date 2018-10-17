use failure::Error;
use std::path::Path;
use std::path::PathBuf;

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
    /// Invoke `git status` and return the result.
    ///
    /// If the git working copy is clean, an empty vec is returned.
    fn status(&self) -> Result<Vec<FileStatus>, Error>;
}

pub struct SystemGit {
    /// The path of the git binary to execute.
    git_path: PathBuf,

    /// The path to the git repository; equivalent of the -C argument to git.
    repo_path: PathBuf,
}

impl SystemGit {
    pub fn new() -> SystemGit {
        SystemGit {
            git_path: PathBuf::from("git"),
            repo_path: PathBuf::from("."),
        }
    }

    pub fn git_path<'a>(&'a mut self, path: &Path) -> &'a mut SystemGit {
        self.git_path = PathBuf::from(path);
        self
    }

    pub fn repo_path<'a>(&'a mut self, path: &Path) -> &'a mut SystemGit {
        self.repo_path = PathBuf::from(path);
        self
    }
}

impl Git for SystemGit {
    fn status(&self) -> Result<Vec<FileStatus>, Error> {
        Err(format_err!("not yet implemented"))
    }
}
