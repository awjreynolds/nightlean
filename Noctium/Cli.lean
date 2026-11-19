import Noctium.Target

namespace Noctium.Cli

def version : String := "0.1.0"

def usage : String := "Noctium " ++ version ++ "\n\
Usage: noctium --version\n\
       noctium profiles\n\
       noctium check <file> [--target <manifest>]\n\
       noctium compile <file> [--target <manifest>] [--output <new-or-empty-directory>]\n\
Default target: profiles/midnight-ledger-9.json\n\
The selectable ZKIR 3.2.1 profile qualifies a selected native subset only."

structure Options where
  input : String
  target : String := "profiles/midnight-ledger-9.json"
  output : String := "build/noctium"
  deriving Repr

private def parseOptions (input : String) (args : List String) (compiling : Bool) :
    Except String Options := go { input } args false false
where
  go (opts : Options) (args : List String) (hasTarget hasOutput : Bool) :
      Except String Options :=
    match args with
    | [] => .ok opts
    | "--target" :: value :: rest =>
      if hasTarget then .error "duplicate --target option"
      else if value.startsWith "--" then .error "--target requires a manifest path"
      else go { opts with target := value } rest true hasOutput
    | "--output" :: value :: rest =>
      if !compiling then .error "--output is only supported by compile"
      else if hasOutput then .error "duplicate --output option"
      else if value.startsWith "--" then .error "--output requires a directory"
      else go { opts with output := value } rest hasTarget true
    | ["--target"] => .error "--target requires a manifest path"
    | ["--output"] => .error "--output requires a directory"
    | arg :: _ => .error s!"unexpected argument '{arg}'"

private def error (message : String) : IO UInt32 := do
  (← IO.getStderr).putStrLn s!"noctium: error: {message}"
  return 1

private def runFrontend (input source command : String) : IO IO.Process.Output :=
  IO.Process.output
    {cmd := "lake", args := #["env", "lean", "-D", "Elab.async=false", "--stdin", input]}
    (some ("import Noctium.Compiler " ++ source ++ "\n" ++ command ++ "\n"))

private def compile (opts : Options) (source profileLiteral : String) : IO IO.Process.Output := do
  let path : System.FilePath := opts.output
  let path := System.FilePath.mk
    ((path.normalize.toString.dropEndWhile (· == System.FilePath.pathSeparator)).toString)
  unless path.fileName.isSome do
    throw (IO.userError "--output requires a new or empty directory")
  if ← path.pathExists then
    unless (← path.isDir) && (← path.readDir).isEmpty do
      throw (IO.userError s!"output '{opts.output}' must be a new or empty directory")
  let parent := path.parent.getD "."
  IO.FS.createDirAll parent
  let stage := parent / s!".noctium-{← IO.Process.getPID}-{← IO.monoNanosNow}"
  IO.FS.createDir stage
  let result ← try
    let directory := (Lean.toJson stage.toString).compress
    let display := (Lean.toJson opts.output).compress
    let result ← runFrontend opts.input source
      s!"#noctium_compile_target {directory} {profileLiteral} {display}"
    if result.exitCode == 0 then
      -- Publish the complete bundle only after Lean has reported all source diagnostics.
      IO.FS.rename stage path
    pure result
  finally
    if ← stage.pathExists then IO.FS.removeDirAll stage
  return result

private def process (opts : Options) (compiling : Bool) : IO UInt32 := do
  let profile ← match ← TargetProfile.load opts.target with
  | .error message => return ← error message
  | .ok profile => pure profile
  let profileJson := (Lean.toJson profile).compress
  let profileLiteral := (Lean.toJson profileJson).compress
  let source ← try IO.FS.readFile opts.input catch _ =>
    return ← error s!"cannot read source '{opts.input}'"
  if source.trimAscii.toString.startsWith "module" then
    return ← error "Lean module-mode files are not part of the current Noctium source surface"
  -- Lean accepts a filename with --stdin. This keeps module identity and source diagnostics,
  -- avoids a temporary source file, and preserves line numbers by placing the extra import
  -- on the original first line. Inputs are trusted Lean source, like `lake env lean` itself.
  let result ← try
    if compiling then compile opts source profileLiteral
    else runFrontend opts.input source s!"#noctium_check_target {profileLiteral}"
  catch e => return ← error e.toString
  (← IO.getStdout).putStr result.stdout
  (← IO.getStderr).putStr result.stderr
  return result.exitCode

def run (args : List String) : IO UInt32 := do
  match args with
  | [] | ["--help"] | ["-h"] =>
    IO.println usage
    return 0
  | ["--version"] =>
    IO.println s!"Noctium {version} (Lean {Lean.versionString})"
    return 0
  | ["profiles"] =>
    IO.println "midnight-ledger-9 profiles/midnight-ledger-9.json source-baseline-unqualified"
    IO.println "midnight-ledger-9-zkir-3.2.1 profiles/midnight-ledger-9-zkir-3.2.1-target.json selected-native-subset-qualified"
    return 0
  | command :: input :: rest =>
    if command != "check" && command != "compile" then
      return ← error s!"unknown command '{command}'"
    if input.startsWith "--" then return ← error "expected a source path"
    match parseOptions input rest (command == "compile") with
    | .error message => return ← error message
    | .ok opts => process opts (command == "compile")
  | ["check"] | ["compile"] => error "expected a source path"
  | command :: _ => error s!"unknown command '{command}'"

end Noctium.Cli
