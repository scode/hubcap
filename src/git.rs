use anyhow::anyhow;
use anyhow::Error;
use anyhow::Result;
use regex::Regex;
use std::collections::HashMap;
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

/// A ref and its associated sha (hash value).
#[derive(Clone, Debug, PartialEq)]
pub struct ResolvedRef {
    name: String,
    sha: String,
}

impl ResolvedRef {
    /// Return the name of the ref.
    ///
    /// Example ref names include:
    ///
    /// ```text
    /// HEAD
    /// refs/heads/master
    /// refs/heads/my-branch
    /// refs/tags/a-tag
    /// refs/remotes/origin/my-branch
    /// ```
    ///
    /// For assistance in interpreting a ref name, see interpret_ref().
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Return the sha the ref refers to.
    ///
    /// The name "sha" is used only because it is the colloquial name, and isn't meant to imply
    /// anything about the choice of hashing algorithm by git.
    pub fn sha(&self) -> &str {
        &self.sha
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum InterpretedRef {
    /// The special HEAD ref (see also: git show-ref --head). This typically indicates the current branch
    /// unless the repo is in a detached head state.
    ///
    /// Examples (only one possibility):
    ///
    /// ```text
    /// HEAD
    /// ```
    Head(),

    /// A tag by the given name.
    ///
    /// Example refs:
    ///
    /// ```text
    /// refs/tags/v1.0.0 -> Tag(v1.0.0)
    /// refs/tags/my/tag -> Tag(my/tag)
    /// ```
    Tag(String),

    /// A local branch.
    ///
    /// Example refs:
    ///
    /// ```text
    /// refs/heads/master -> LocalBranch(master)
    /// refs/heads/my/branch -> LocalBranch(my/branch)
    /// ```
    LocalBranch(String),

    /// A remote branch by the given name on the given remote.
    ///
    /// Example refs:
    ///
    /// ```text
    /// refs/remotes/origin/master -> RemoteBranch(origin, master)
    /// refs/remotes/upstream/some/branch -> RemoteBranch(upstream, some/branch)
    /// ```
    RemoteBranch { remote: String, name: String },
}

/// Interpret a ref name if possible.
///
/// See InterpretedRef and its comments for what we consider to be valid refs.
///
/// We return an error if we cannot recognize the ref.
///
/// ```
/// # use hubcap::git::interpret_ref;
/// # use hubcap::git::InterpretedRef;
/// assert_eq!(interpret_ref("HEAD").unwrap(), InterpretedRef::Head());
/// assert_eq!(interpret_ref("refs/heads/master").unwrap(), InterpretedRef::LocalBranch("master".into()));
/// assert_eq!(interpret_ref("refs/heads/my/branch").unwrap(), InterpretedRef::LocalBranch("my/branch".into()));
/// assert_eq!(interpret_ref("refs/tags/v1.0.0").unwrap(), InterpretedRef::Tag("v1.0.0".into()));
/// assert_eq!(interpret_ref("refs/tags/betas/v1.0.0-b1").unwrap(), InterpretedRef::Tag("betas/v1.0.0-b1".into()));
/// assert_eq!(interpret_ref("refs/remotes/origin/master").unwrap(), InterpretedRef::RemoteBranch{remote: "origin".into(), name: "master".into()});
/// assert_eq!(interpret_ref("refs/remotes/upstream/some/branch").unwrap(), InterpretedRef::RemoteBranch{remote: "upstream".into(), name: "some/branch".into()});
/// assert!(interpret_ref("invalid").is_err());
/// ```
pub fn interpret_ref<T: AsRef<str>>(ref_name: T) -> Result<InterpretedRef, Error> {
    // Should consider using lazy_static crate to cache.
    let re = Regex::new(r"^(?P<head>HEAD)|refs/tags/(?P<tag>.*)|refs/heads/(?P<localbranch>.*)|refs/remotes/(?P<remote>[^/]+)/(?P<remotebranch>.*)$").unwrap();
    let capture = re
        .captures(ref_name.as_ref())
        .ok_or_else(|| anyhow!("could not interpret ref: [{}]", ref_name.as_ref()))?;

    let head = capture.name("head");
    if head.is_some() {
        return Ok(InterpretedRef::Head());
    }

    let tag = capture.name("tag");
    if let Some(tag) = tag {
        return Ok(InterpretedRef::Tag(tag.as_str().into()));
    }

    let local_branch = capture.name("localbranch");
    if let Some(local_branch) = local_branch {
        return Ok(InterpretedRef::LocalBranch(local_branch.as_str().into()));
    }

    let origin = capture.name("remote");
    if let Some(origin) = origin {
        match capture.name("remotebranch") {
            Some(remote_branch) => {
                return Ok(InterpretedRef::RemoteBranch {
                    remote: origin.as_str().into(),
                    name: remote_branch.as_str().into(),
                })
            }
            None => return Err(anyhow!("bug: rematched remote but not remotebranch")),
        }
    }

    Err(anyhow!("caould not interpret ref: {}", ref_name.as_ref()))
}

pub trait Git {
    /// Initialize a repo (`git init`).
    fn init(&self) -> Result<(), Error>;

    /// Inspect the status of the working copy and return a description of it.
    ///
    /// This is the equivalent of `git status`.
    ///
    /// If the git working copy is clean, an empty vec is returned.
    fn status(&self) -> Result<Vec<StatusEntry>, Error>;

    /// Return all refs known to git.
    ///
    /// If the repo has no refs (typically a freshly initialized empty repo), an error
    /// is returned (this is arguably unexpected, but fits the behavior of show-ref).
    fn refs(&self) -> Result<Vec<ResolvedRef>, Error>;

    /// Set a --local configuration value (`git config --local key value`).
    ///
    /// Any existing value will be overwritten.
    ///
    /// The key must start with a section name followed by a period - see git-config(1).
    fn config_local_set(&self, key: &str, val: &str) -> Result<(), Error>;

    /// Unset a --local configuration value (`git config --local --unset key`).
    ///
    /// If the key does not exist, it is considered an error.
    fn config_local_unset(&self, key: &str) -> Result<(), Error>;

    /// List all --local configuration values (`git config --local --list`).
    fn config_local_list(&self) -> Result<HashMap<String, String>, Error>;

    /// Get a configuration value, if present (`git config --local --get`).
    fn config_local_get(&self, key: &str) -> Result<Option<String>, Error>;
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
    fn init(&self) -> Result<(), Error> {
        let mut cmd = self.git_command()?;

        cmd.arg("init").arg("-q");

        let output = cmd.output()?;

        if !output.status.success() {
            return Err(anyhow!(
                "git init failed: {}",
                String::from_utf8(output.stderr)?
            ));
        }

        Ok(())
    }

    fn status(&self) -> Result<Vec<StatusEntry>, Error> {
        let mut cmd = self.git_command()?;

        cmd.arg("status").arg("-z");

        let output = cmd.output()?;

        if !output.status.success() {
            return Err(anyhow!(
                "git terminated in error: {}",
                String::from_utf8(output.stderr)?
            ));
        }

        let stdout = String::from_utf8(output.stdout)?;

        let mut lines: Vec<&str> = stdout.split('\0').collect();
        if *lines.last().unwrap() != "" {
            return Err(anyhow!(
                "expected trailing zero in git status output; got none"
            ));
        }
        lines.pop();
        status_lines_to_entries(lines)
    }

    fn refs(&self) -> Result<Vec<ResolvedRef>, Error> {
        let mut cmd = self.git_command()?;

        cmd.arg("show-ref").arg("--head");

        let output = cmd.output()?;
        if !output.status.success() {
            return Err(anyhow!(
                "git show-ref terminated in error: {}",
                String::from_utf8(output.stderr)?
            ));
        }

        let stdout = String::from_utf8(output.stdout)?;

        stdout.lines().map(sha_ref_to_resolved_ref).collect()
    }

    fn config_local_set(&self, key: &str, val: &str) -> Result<(), Error> {
        let mut cmd = self.git_command()?;

        cmd.arg("config").arg("--local").arg(key).arg(val);

        let output = cmd.output()?;
        if !output.status.success() {
            return Err(anyhow!(
                "git config terminated in error: {}",
                String::from_utf8(output.stderr)?
            ));
        }

        Ok(())
    }

    fn config_local_unset(&self, key: &str) -> Result<(), Error> {
        let mut cmd = self.git_command()?;

        cmd.arg("config").arg("--local").arg("--unset").arg(key);

        let output = cmd.output()?;
        if !output.status.success() {
            return Err(anyhow!(
                "git config terminated in error: {}",
                String::from_utf8(output.stderr)?
            ));
        }

        Ok(())
    }

    fn config_local_list(&self) -> Result<HashMap<String, String>, Error> {
        let mut cmd = self.git_command()?;

        cmd.arg("config").arg("--local").arg("--list").arg("-z");

        let output = cmd.output()?;
        if !output.status.success() {
            return Err(anyhow!(
                "git config terminated in error: {}",
                String::from_utf8(output.stderr)?
            ));
        }

        let mut items: HashMap<String, String> = HashMap::new();

        // When -z is used, newlines are used to delimit keys from values and a zero byte is used
        // to indicate the end of a value (note: values may contain newlines).
        let stdout = String::from_utf8(output.stdout)?;
        let chars = stdout.chars();

        let mut key = String::new();
        let mut value = String::new();
        let mut inkey = true;

        for c in chars {
            if inkey {
                if c == '\n' {
                    inkey = false;
                    continue;
                }
                key.push(c)
            } else {
                if c == '\0' {
                    inkey = true;
                    items.insert(key.clone(), value.clone());
                    key.clear();
                    value.clear();
                    continue;
                }
                value.push(c)
            }
        }

        if !key.is_empty() || !value.is_empty() {
            return Err(anyhow!("git config --local --list output parsing ended on unexpected byte; we expect the final byte to be a zero"));
        }

        Ok(items)
    }

    fn config_local_get(&self, key: &str) -> Result<Option<String>, Error> {
        // Git does not offer a documented way of differentiating between "config key does not
        // exist" and any other failure. As a result, we implement this in terms of
        // config_local_list() instead of using the --get option.
        let items = self.config_local_list()?;

        Ok(items.get(key).map(|s| s.to_owned()))
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
        _ => Err(anyhow!("unrecognized status: {}", status)),
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

/// Convert a line of show-ref output into a ResolvedRef.
fn sha_ref_to_resolved_ref<T: Into<String>>(line: T) -> Result<ResolvedRef, Error> {
    // XXX: Would prefer iterators over array indexing for safety.
    let s: String = line.into();
    let v: Vec<&str> = s.split_whitespace().collect();
    if v.len() != 2 {
        return Err(anyhow!("expected sha followed by ref name, got: {}", s));
    }

    Ok(ResolvedRef {
        sha: v[0].into(),
        name: v[1].into(),
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
fn status_lines_to_entries<'a>(
    lines: impl IntoIterator<Item = &'a str>,
) -> Result<Vec<StatusEntry>, Error> {
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
            let capture = status_regex().captures(line).ok_or_else(|| {
                anyhow!(
                    "unexpected git status line (does not match regex): [{}]",
                    line
                )
            })?;
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
        return Err(anyhow!(
            "encountered renamed/copied status with no subsequent follow-up line"
        ));
    }

    Ok(entries)
}

fn status_regex() -> Regex {
    // Should consider using lazy_static crate to cache.
    Regex::new(r"^(?P<x>[ MADRCU?])(?P<y>[ MADRCU?]) (?P<rest>.*)$").unwrap()
}

/// Convert a Path to a String, failing with an error if the string is not valid utf-8.
///
/// Future: Use https://doc.rust-lang.org/std/option/struct.NoneError.html when stable?
fn path_to_str(p: &Path) -> Result<String, Error> {
    p.to_str()
        .ok_or_else(|| anyhow!("path is not valid utf-8: {:?}", p))
        .map(std::borrow::ToOwned::to_owned)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs::File;
    use tempdir;

    fn configured_git(repo_path: &Path) -> SystemGit {
        let mut git = SystemGit::new();
        git.repo_path(repo_path);

        check_output(Command::new("git").arg("-C").arg(repo_path).arg("init")).unwrap();

        check_output(
            Command::new("git")
                .arg("-C")
                .arg(repo_path)
                .arg("config")
                .arg("--local")
                .arg("user.email")
                .arg("hubcabtest@example.com"),
        )
        .unwrap();

        check_output(
            Command::new("git")
                .arg("-C")
                .arg(repo_path)
                .arg("config")
                .arg("--local")
                .arg("user.name")
                .arg("hubcabtest"),
        )
        .unwrap();

        git
    }

    fn check_output(cmd: &mut Command) -> Result<(), Error> {
        let output = cmd.output()?;
        if !output.status.success() {
            return Err(anyhow!(
                "cmd exited unsuccessfully: stdout: {} stderr: {}",
                String::from_utf8(output.stdout)?,
                String::from_utf8(output.stderr)?,
            ));
        }

        Ok(())
    }

    #[test]
    fn test_git_init() {
        let tmp_dir = tempdir::TempDir::new("hubcap-test").unwrap();
        let tmp_path = tmp_dir.path();
        let git = configured_git(tmp_path);

        git.init().expect("git init failed");
        assert!(tmp_path.join(".git").exists());
    }

    #[test]
    fn test_system_git_status() {
        let tmp_dir = tempdir::TempDir::new("hubcap-test").unwrap();
        let tmp_path = tmp_dir.path();
        let mut git = SystemGit::new();
        git.repo_path(tmp_path);

        // An entirely clean working copy (catch special case of git status returning no output).
        {
            check_output(Command::new("git").arg("-C").arg(tmp_path).arg("init")).unwrap();
            let status = git.status().unwrap();
            assert_eq!(status.len(), 0)
        }

        // Non-empty status output (untracked file).
        {
            File::create(tmp_path.join("testfile")).unwrap();

            let status = git.status().unwrap();
            assert_eq!(status.len(), 1);
            assert_eq!(
                status[0],
                StatusEntry {
                    merge_or_index: Status::Untracked(PathBuf::from("testfile")),
                    work_tree: Status::Untracked(PathBuf::from("testfile")),
                }
            )
        }

        tmp_dir.close().unwrap();
    }

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
    fn test_status_lines_to_entries_empty_vec() {
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

        status_regex().captures("?? file").unwrap();
        status_regex().captures("MM file").unwrap();
        status_regex().captures("AA file").unwrap();
        status_regex().captures("DD file").unwrap();
        status_regex().captures("RR file").unwrap();
        status_regex().captures("CC file").unwrap();
        status_regex().captures("UU file").unwrap();
        status_regex().captures("   file").unwrap();
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

    #[test]
    fn test_interpret_ref_unrecognized() {
        assert!(interpret_ref("random").is_err());
    }

    #[test]
    fn test_interpret_ref_head() {
        assert_eq!(interpret_ref("HEAD").unwrap(), InterpretedRef::Head());
    }

    #[test]
    fn test_interpret_ref_tag() {
        assert_eq!(
            interpret_ref("refs/tags/tagname").unwrap(),
            InterpretedRef::Tag("tagname".into())
        );
        assert_eq!(
            interpret_ref("refs/tags/tag/name").unwrap(),
            InterpretedRef::Tag("tag/name".into())
        );
    }

    #[test]
    fn test_interpret_ref_local_branch() {
        assert_eq!(
            interpret_ref("refs/heads/branch").unwrap(),
            InterpretedRef::LocalBranch("branch".into())
        );
        assert_eq!(
            interpret_ref("refs/heads/branch/name").unwrap(),
            InterpretedRef::LocalBranch("branch/name".into())
        );
    }

    #[test]
    fn test_interpret_ref_remote_branch() {
        assert_eq!(
            interpret_ref("refs/remotes/origin/branch/name").unwrap(),
            InterpretedRef::RemoteBranch {
                remote: "origin".into(),
                name: "branch/name".into()
            }
        );
    }

    #[test]
    fn test_sha_ref_to_resolved_ref() {
        assert_eq!(
            sha_ref_to_resolved_ref("abc ref/name").unwrap(),
            ResolvedRef {
                name: "ref/name".into(),
                sha: "abc".into()
            }
        );
        assert!(sha_ref_to_resolved_ref("").is_err());
        assert!(sha_ref_to_resolved_ref("abc").is_err());
        assert!(sha_ref_to_resolved_ref("abc name garbage").is_err());
    }

    #[test]
    fn test_system_git_refs_non_empty() {
        use std::io::prelude::*;
        let tmp_dir = tempdir::TempDir::new("hubcap-test").unwrap();
        let tmp_path = tmp_dir.path();
        let git = configured_git(tmp_path);

        check_output(Command::new("git").arg("-C").arg(tmp_path).arg("init")).unwrap();

        let mut f = File::create(tmp_path.join("testfile")).unwrap();
        f.write_all("test".as_bytes()).unwrap();

        check_output(
            Command::new("git")
                .arg("-C")
                .arg(tmp_path)
                .arg("add")
                .arg("testfile"),
        )
        .unwrap();

        check_output(
            Command::new("git")
                .arg("-C")
                .arg(tmp_path)
                .arg("commit")
                .arg("-m")
                .arg("testcommit")
                .arg("testfile"),
        )
        .unwrap();

        let refs = git.refs().unwrap();
        assert_eq!(refs.len(), 2);
        assert_eq!(refs[0].name, "HEAD");
        assert_eq!(refs[1].name, "refs/heads/master");
    }

    #[test]
    /// Test refs() on an empty repo (without a commit).
    fn test_system_git_refs_empty() {
        let tmp_dir = tempdir::TempDir::new("hubcap-test").unwrap();
        let tmp_path = tmp_dir.path();
        let git = configured_git(tmp_path);

        check_output(Command::new("git").arg("-C").arg(tmp_path).arg("init")).unwrap();

        assert!(git.refs().is_err());
    }

    #[test]
    fn test_system_git_config_basics() {
        let tmp_dir = tempdir::TempDir::new("hubcap-test").unwrap();
        let tmp_path = tmp_dir.path();
        let git = configured_git(tmp_path);

        check_output(Command::new("git").arg("-C").arg(tmp_path).arg("init")).unwrap();

        assert_eq!(git.config_local_get("hubcap.test").unwrap(), None);

        git.config_local_set("hubcap.test", "val").unwrap();

        assert_eq!(
            git.config_local_get("hubcap.test").unwrap(),
            Some("val".into())
        );

        let items = git.config_local_list().unwrap();
        assert!(items.contains_key("hubcap.test"));

        git.config_local_unset("hubcap.test").unwrap();
        assert_eq!(git.config_local_get("hubcap.test").unwrap(), None);

        let items = git.config_local_list().unwrap();
        assert!(!items.contains_key("hubcap.test"));

        // Test that newlines in values are handled correctly.
        git.config_local_set("hubcap.test", "a\nb").unwrap();
        assert_eq!(
            git.config_local_get("hubcap.test").unwrap(),
            Some("a\nb".into())
        );

        // Test that empty values are handled correctly.
        git.config_local_set("hubcap.test", "").unwrap();
        assert_eq!(
            git.config_local_get("hubcap.test").unwrap(),
            Some("".into())
        );
    }
}
