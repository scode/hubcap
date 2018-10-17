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
