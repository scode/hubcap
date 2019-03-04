use failure::Error;
use regex::Regex;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;

/// The possible states a file can be in.
///
/// See also: StatusEntry
#[derive(Clone, Debug, PartialEq)]
pub enum Status {
    /// Clean is the absense of any other status (what is represented as whitespace in "git status" output"). This can occur because
    /// the file has a non-clean in the other "arm" of the status entry. For example, if the file is clean in the index but modified
    /// in the work tree, it will result in a StatusEntry whose index side will be Clean(...).
    Clean(PathBuf),
    Modified(PathBuf),
    Added(PathBuf),
    Deleted(PathBuf),
    Renamed {
        new: PathBuf,
        old: PathBuf,
    },
    Copied {
        new: PathBuf,
        old: PathBuf,
    },
    UpdatedUnMerged(PathBuf),
    Untracked(PathBuf),
}

/// A status "line" as reported by `git status`.
///
/// Please see git-status(1) for more.
#[derive(Clone, Debug, PartialEq)]
pub struct StatusEntry {
    /// The "X" as described in git-status(1). It can represent the other side of a merge with
    /// conflicts, or the status in the index, depending on the state of the repo.
    pub merge_or_index: Status,

    /// The "Y" as described in git-status(1). Represents the status of the file in the local
    /// work tree.
    pub work_tree: Status,
}

pub trait Git {
    /// Inspect the status of the working copy and return a description of it.
    ///
    /// This is the equivalent of `git status`.
    ///
    /// If the git working copy is clean, an empty vec is returned.
    fn status(&self) -> Result<Vec<StatusEntry>, Error>;
}

/// An implementation of the Git trait which uses a git binary present on the system to interact
/// with a git repository.
#[derive(Default)]
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
    fn status(&self) -> Result<Vec<StatusEntry>, Error> {
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

        let lines: Vec<&str> = stdout.split('\0').collect();

        status_lines_to_entries(lines.into_iter())
    }
}

fn make_status(status: &str, rest: &str, next_line: Option<&str>) -> Result<Status, Error> {
    match status {
        "M" => Ok(Status::Modified(PathBuf::from(rest))),
        "A" => Ok(Status::Added(PathBuf::from(rest))),
        "D" => Ok(Status::Deleted(PathBuf::from(rest))),
        "R" => Ok(Status::Renamed {
            new: PathBuf::from(rest),
            old: PathBuf::from(next_line.unwrap()),
        }),
        "C" => Ok(Status::Copied {
            new: PathBuf::from(rest),
            old: PathBuf::from(next_line.unwrap()),
        }),
        "U" => Ok(Status::UpdatedUnMerged(PathBuf::from(rest))),
        "?" => Ok(Status::Untracked(PathBuf::from(rest))),
        " " => Ok(Status::Clean(PathBuf::from(rest))),
        _ => Err(format_err!("unrecognized status: {}", status)),
    }
}

fn make_status_entry(
    x: &str,
    y: &str,
    rest: &str,
    next_line: Option<&str>,
) -> Result<StatusEntry, Error> {
    Ok(StatusEntry {
        merge_or_index: make_status(x, rest, next_line)?,
        work_tree: make_status(y, rest, next_line)?,
    })
}

/// Given a sequence of lines (obtained from `git status -z`), produce the corresponding set of
/// status entries.
///
/// In short, for statuses other than renamed/copied we expect:
///
///    <STATUS FLAG OR SPACE> <STATUS FLAG> <SPACE> <ANY CHARS EXCEPT NUL REPEATED> NUL
///
/// For renamed/copied statuses, an additional <ANY CHARS EXCEPT NUL> NUL is used.
///
/// Example:
///   MM modified.txt
///    M modified_in_worktree.txt
///   ?? untracked.txt
///    R newfile.txt
///   oldfile.txt
///
/// See git-status(1) for more.
fn status_lines_to_entries<'a, I>(lines: I) -> Result<Vec<StatusEntry>, Error>
where
    I: Iterator<Item = &'a str>,
{
    let mut entries: Vec<StatusEntry> = Vec::new();

    // This function isn't a straight forward use of map because of the potential for an "entry" to span two
    // lines (renames and copies). We keep an optional previous line around, whose presence indicates we are
    // processing either a rename or a copy, in which case we must defer our call to make_status_entry() until
    // we have read the follow-up line.
    //
    // XXX(scode): There's almost certainly a more idiomatic implementation of this using combinators. Sorry people.
    struct XYRest {
        x: String,
        y: String,
        rest: String,
    };
    let mut maybe_partial_status: Option<XYRest> = None;
    for line in lines {
        if let Some(partial_status) = maybe_partial_status {
            entries.push(make_status_entry(
                &partial_status.x,
                &partial_status.y,
                &partial_status.rest,
                Some(line),
            )?);
            maybe_partial_status = None;
        } else {
            let capture = status_regex()
                .captures(line)
                .ok_or_else(|| format_err!("unexpected git status line: {}", line))?;
            let x = capture.name("x").unwrap().as_str();
            let y = capture.name("y").unwrap().as_str();
            let rest = capture.name("rest").unwrap().as_str();

            if x == "C" || x == "R" || y == "C" || y == "R" {
                maybe_partial_status = Some(XYRest {
                    x: x.to_owned(),
                    y: y.to_owned(),
                    rest: rest.to_owned(),
                })
            } else {
                entries.push(make_status_entry(x, y, rest, None)?);
            }
        }
    }

    if maybe_partial_status.is_some() {
        bail!("encountered renamed/copied status wiht no subsequent follow-up line");
    }

    Ok(entries)
}

fn status_regex() -> Regex {
    Regex::new(r"^(?P<x>[ MADRCU])(?P<y>[ MADRCU]) (?P<rest>.*)$").unwrap()
}

/// Convert a Path to a String, failing with an error if the string is not valid utf-8.
///
/// Future: Use https://doc.rust-lang.org/std/option/struct.NoneError.html when stable?
fn path_to_str(p: &Path) -> Result<String, Error> {
    p.to_str()
        .ok_or_else(|| format_err!("path is not valid utf-8: {:?}", p))
        .map(std::borrow::ToOwned::to_owned)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_make_status() {
        let s = make_status("M", "path", None);
        assert!(s.is_ok());
        assert_eq!(s.unwrap(), Status::Modified(PathBuf::from("path")));

        let s = make_status("A", "path", None);
        assert!(s.is_ok());
        assert_eq!(s.unwrap(), Status::Added(PathBuf::from("path")));

        let s = make_status("D", "path", None);
        assert!(s.is_ok());
        assert_eq!(s.unwrap(), Status::Deleted(PathBuf::from("path")));

        let s = make_status("R", "newpath", Some("oldpath"));
        assert!(s.is_ok());
        assert_eq!(
            s.unwrap(),
            Status::Renamed {
                new: PathBuf::from("newpath"),
                old: PathBuf::from("oldpath"),
            }
        );

        let s = make_status("C", "newpath", Some("oldpath"));
        assert!(s.is_ok());
        assert_eq!(
            s.unwrap(),
            Status::Copied {
                new: PathBuf::from("newpath"),
                old: PathBuf::from("oldpath"),
            }
        );

        let s = make_status("?", "path", None);
        assert!(s.is_ok());
        assert_eq!(s.unwrap(), Status::Untracked(PathBuf::from("path")));

        let s = make_status(" ", "path", None);
        assert!(s.is_ok());
        assert_eq!(s.unwrap(), Status::Clean(PathBuf::from("path")));

        let s = make_status("random", "path", None);
        assert!(s.is_err());
    }

    #[test]
    fn test_status_lines_to_entries_empty() {
        let r = status_lines_to_entries(vec![].into_iter());
        assert!(r.is_ok());
        assert!(r.unwrap().len() == 0);
    }

    #[test]
    fn test_status_lines_to_entries_both_single_line() {
        let r = status_lines_to_entries(vec!["MD file.txt"].into_iter());
        assert!(r.is_ok());
        let v = r.unwrap();
        assert_eq!(v.len(), 1);
        assert_eq!(
            v,
            vec![StatusEntry {
                merge_or_index: Status::Modified(PathBuf::from("file.txt")),
                work_tree: Status::Deleted(PathBuf::from("file.txt")),
            }]
        );
    }

    #[test]
    fn test_status_lines_to_entries_copied_right() {
        let r = status_lines_to_entries(vec![" C new.txt", "old.txt"].into_iter());
        assert!(r.is_ok());
        let v = r.unwrap();
        assert_eq!(v.len(), 1);
        assert_eq!(
            v,
            vec![StatusEntry {
                merge_or_index: Status::Clean(PathBuf::from("new.txt")),
                work_tree: Status::Copied {
                    new: PathBuf::from("new.txt"),
                    old: PathBuf::from("old.txt"),
                },
            }]
        );
    }

    #[test]
    fn test_status_lines_to_entries_copied_left() {
        let r = status_lines_to_entries(vec!["C  new.txt", "old.txt"].into_iter());
        assert!(r.is_ok());
        let v = r.unwrap();
        assert_eq!(v.len(), 1);
        assert_eq!(
            v,
            vec![StatusEntry {
                merge_or_index: Status::Copied {
                    new: PathBuf::from("new.txt"),
                    old: PathBuf::from("old.txt"),
                },
                work_tree: Status::Clean(PathBuf::from("new.txt")),
            }]
        );
    }

    #[test]
    fn test_status_lines_to_entries_renamed_right() {
        let r = status_lines_to_entries(vec![" R new.txt", "old.txt"].into_iter());
        assert!(r.is_ok());
        let v = r.unwrap();
        assert_eq!(v.len(), 1);
        assert_eq!(
            v,
            vec![StatusEntry {
                merge_or_index: Status::Clean(PathBuf::from("new.txt")),
                work_tree: Status::Renamed {
                    new: PathBuf::from("new.txt"),
                    old: PathBuf::from("old.txt"),
                },
            }]
        );
    }

    #[test]
    fn test_status_lines_to_entries_renamed_left() {
        let r = status_lines_to_entries(vec!["R  new.txt", "old.txt"].into_iter());
        assert!(r.is_ok());
        let v = r.unwrap();
        assert_eq!(v.len(), 1);
        assert_eq!(
            v,
            vec![StatusEntry {
                merge_or_index: Status::Renamed {
                    new: PathBuf::from("new.txt"),
                    old: PathBuf::from("old.txt"),
                },
                work_tree: Status::Clean(PathBuf::from("new.txt")),
            }]
        );
    }

    #[test]
    fn test_status_lines_to_entries_truncated_expecting_second_line() {
        let r = status_lines_to_entries(
            vec![
                " C file.txt", // should be followd by another line
            ]
            .into_iter(),
        );
        assert!(r.is_err());

        let r = status_lines_to_entries(
            vec![
                " R file.txt", // should be followd by another line
            ]
            .into_iter(),
        );
        assert!(r.is_err());
    }

    #[test]
    fn status_regex_correct() {
        let cap = status_regex().captures("AM fname").unwrap();
        assert_eq!(cap.name("x").unwrap().as_str(), "A");
        assert_eq!(cap.name("y").unwrap().as_str(), "M");
        assert_eq!(cap.name("rest").unwrap().as_str(), "fname");

        assert!(status_regex().captures(" AM fname").is_none());
        assert!(status_regex().captures("AMM fname").is_none());
        assert!(status_regex().captures("AM").is_none());
        assert!(status_regex().captures("AM").is_none());
    }

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
