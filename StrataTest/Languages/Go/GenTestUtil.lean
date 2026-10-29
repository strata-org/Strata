/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Lean.Elab.Command
public meta import Strata.Go.Gen

namespace Strata.Go.TestUtil

public meta def check (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- Look up one generated file by name, or log and return `""`. -/
public meta def fileNamed (files : GeneratedFiles) (name : String) :
    Lean.Elab.Command.CommandElabM String := do
  match files.files.find? (·.1 == name) with
  | some (_, content) => return content
  | none =>
    Lean.logError s!"Expected generated file {name}"
    return ""

/--
Whether the Go checks must run rather than skip: inside a Brazil build, or under
CI (`CI` set, as GitHub Actions and most CI systems do).

Test files under `StrataTestExtra/` run as `lean <file>` children of the test
driver, which prints only `PASS: <module>` for a zero exit. A skip warning is
therefore invisible to everyone but a developer running the file by hand, and on
a CI run it would turn every Go suite into a silent pass.
-/
public def goChecksRequired : IO Bool := do
  if (← IO.getEnv "BRAZIL_BUILD_HOME").isSome then return true
  match ← IO.getEnv "CI" with
  | some v => return !v.isEmpty && v != "0" && v.toLower != "false"
  | none => return false

/--
Whether a working Go toolchain is on `PATH`.

Local development may omit Go and skip the generated-code checks. A Brazil build
must provide Go through `build-tools`, and a CI run must install it; in both an
absent toolchain is a hard failure (see `goChecksRequired`).
-/
public def haveGo : IO Bool := do
  let required ← goChecksRequired
  let result ←
    try
      pure (some (← IO.Process.output { cmd := "go", args := #["version"] }))
    catch _ =>
      pure none
  match result with
  | some r =>
    if r.exitCode == 0 then return true
    if required then
      throw <| IO.userError s!"Go is required in Brazil and CI builds, but \
        `go version` exited {r.exitCode}:\n{r.stdout}\n{r.stderr}"
    return false
  | none =>
    if required then
      throw <| IO.userError s!"Go is required in Brazil and CI builds but is not \
        available on PATH"
    return false

/-- Run a command in `cwd`, returning a failure report when it exits nonzero. -/
public def runTool (cmd : String) (args : Array String) (cwd : System.FilePath) :
    IO (Option String) := do
  let r ← IO.Process.output { cmd, args, cwd }
  if r.exitCode == 0 then return none
  return some s!"`{cmd} {" ".intercalate args.toList}` failed \
                (exit {r.exitCode}):\n{r.stdout}\n{r.stderr}"

/-- The `go` directive written into a test module unless ion-go needs a newer one. -/
def minGoVersion : String := "1.26"

/-- `a < b` for Go versions such as `1.26` or `1.27.2`, compared numerically. -/
def goVersionLt (a b : String) : Bool :=
  let parts (v : String) := (v.splitOn ".").map (·.toNat?.getD 0)
  let rec lt : List Nat → List Nat → Bool
    | [], [] => false
    | [], _ :: _ => true
    | _ :: _, [] => false
    | x :: xs, y :: ys => x < y || (x == y && lt xs ys)
  lt (parts a) (parts b)

/-- The version on the `go` line of `moduleDir/go.mod`, if there is one. -/
def goDirective (moduleDir : System.FilePath) : IO (Option String) := do
  let file := moduleDir / "go.mod"
  unless ← file.pathExists do return none
  for line in (← IO.FS.readFile file).splitOn "\n" do
    match (line.splitOn " ").filter (fun w => w != "" && w != "\r") with
    | ["go", v] => return some v
    | _ => pure ()
  return none

/--
Write a `go.mod` for a generated-code test into `dir` and leave its ion-go
dependency resolvable by the Go tooling that runs next. Call this *after* the Go
sources are in place: resolution outside Brazil reads their imports.

Two environments, two mechanisms:

* **Inside a Brazil build** `brazil-path` resolves the dependency to a local
  source tree and a `replace` points at it. A module replaced by a filesystem
  path needs no checksum, so this stays offline and deterministic, which is what
  the Package Builder sandbox requires.
* **Outside Brazil** the module has to come from the module proxy, and a bare
  `require` is not enough on its own: Go's default `-mod=readonly` refuses to
  build a module whose `go.sum` has no entry for it, so every `go vet`/`go
  build` below would fail with `missing go.sum entry`. `go mod tidy` fetches the
  module and writes both files.

Returns `none` on success, or the reason the caller should report and skip on.
Resolving from the proxy needs the network, so an offline local checkout gets
one clear skip rather than a wall of `missing go.sum entry` failures. Inside
Brazil or under CI a failure here is thrown instead: Go coverage is not allowed
to disappear silently from a build that reports only pass or fail, and `go mod
tidy` reads the generated sources, so a generator regression that breaks it must
fail too. This is the same stance `haveGo` takes.
-/
public def writeGoModule (dir : System.FilePath) (moduleName : String) :
    IO (Option String) := do
  let header (goVersion : String) :=
    s!"module {moduleName}\n\ngo {goVersion}\n\n\
       require github.com/amazon-ion/ion-go v1.3.0\n"
  let brazilIonGo ← do
    try
      let r ← IO.Process.output {
        cmd := "brazil-path"
        args := #["[Go3p-Github-AmazonIon-IonGo]pkg.src"]
      }
      let path := r.stdout.trimAscii
      pure (if r.exitCode == 0 && !path.isEmpty then some path else none)
    catch _ => pure none
  match brazilIonGo with
  | some path =>
    -- Go refuses a main module whose `go` line is older than a dependency's
    -- ("updates to go.mod needed"), and the Brazil build of ion-go declares the
    -- version set's toolchain, so follow it when it is newer.
    let goVersion := match ← goDirective path.toString with
      | some v => if goVersionLt minGoVersion v then v else minGoVersion
      | none => minGoVersion
    IO.FS.writeFile (dir / "go.mod")
      (header goVersion ++ s!"\nreplace github.com/amazon-ion/ion-go => {path}\n")
    return none
  | none =>
    IO.FS.writeFile (dir / "go.mod") (header minGoVersion)
    match ← runTool "go" #["mod", "tidy"] dir with
    | none => return none
    | some err =>
      let reason := s!"ion-go could not be resolved, so the Go checks cannot \
                       run: `brazil-path` did not supply it and `go mod tidy` \
                       failed:\n{err}"
      if ← goChecksRequired then
        throw <| IO.userError reason
      return some reason

/-- Check that a Go module is formatted and passes `go vet`.

`gofmt -l` exits successfully while listing files it would reformat, so both its
exit code and its output must be checked. -/
public def checkGoClean (dir : System.FilePath) : IO (Option String) := do
  let fmt ← IO.Process.output { cmd := "gofmt", args := #["-l", "."], cwd := dir }
  if fmt.exitCode != 0 then return some s!"gofmt failed:\n{fmt.stderr}"
  unless fmt.stdout.trimAscii.isEmpty do
    return some s!"generated Go is not gofmt-clean; gofmt -l listed:\n{fmt.stdout}"
  runTool "go" #["vet", "./..."] dir

/-- Remove any previous test directory and recreate it empty. -/
public def prepareTempDir (dir : System.FilePath) : IO Unit := do
  if ← dir.pathExists then IO.FS.removeDirAll dir
  IO.FS.createDirAll dir

/-- Remove a test directory when it exists. -/
public def cleanupTempDir (dir : System.FilePath) : IO Unit := do
  if ← dir.pathExists then IO.FS.removeDirAll dir

end Strata.Go.TestUtil
