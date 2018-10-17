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
    /// be present in PATH.
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
}

impl Git for SystemGit {
    fn status(&self) -> Result<Vec<FileStatus>, Error> {
        Err(format_err!("not yet implemented"))
    }
}
