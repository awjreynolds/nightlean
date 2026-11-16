import Nightlean.Target

namespace Nightlean.Cli

def version : String := "0.1.0"

def usage : String := "Nightlean " ++ version ++ "\n\
Usage: nightlean --version\n\
       nightlean profiles\n\
       nightlean check <file> [--target <manifest>]\n\
       nightlean compile <file> [--target <manifest>] [--output <directory>] [--adapter compact]\n\
Default target: profiles/midnight-ledger-9.json\n\
Target qualification: source baseline only; no deployable backend qualified."

structure Options where
  input : String
  target : String := "profiles/midnight-ledger-9.json"
  output : String := "build/nightlean"
  compactAdapter : Bool := false
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
    | "--adapter" :: value :: rest =>
      if !compiling then .error "--adapter is only supported by compile"
      else if opts.compactAdapter then .error "duplicate --adapter option"
      else if value != "compact" then .error "unsupported adapter; expected compact"
      else go { opts with compactAdapter := true } rest hasTarget hasOutput
    | ["--target"] => .error "--target requires a manifest path"
    | ["--output"] => .error "--output requires a directory"
    | ["--adapter"] => .error "--adapter requires a name"
    | arg :: _ => .error s!"unexpected argument '{arg}'"

private def error (message : String) : IO UInt32 := do
  (← IO.getStderr).putStrLn s!"nightlean: error: {message}"
  return 1

private def process (opts : Options) (compiling : Bool) : IO UInt32 := do
  match ← TargetProfile.load opts.target with
  | .error message => return ← error message
  | .ok _ => pure ()
  let source ← try IO.FS.readFile opts.input catch _ =>
    return ← error s!"cannot read source '{opts.input}'"
  if source.trimAscii.toString.startsWith "module" then
    return ← error "Lean module-mode files are not part of the current Nightlean source surface"
  -- Lean accepts a filename with --stdin. This keeps module identity and source diagnostics,
  -- avoids a temporary source file, and preserves line numbers by placing the extra import
  -- on the original first line. Inputs are trusted Lean source, like `lake env lean` itself.
  let input := "import Nightlean.Compiler " ++ source ++ "\n#nightlean_check\n"
  let result ← try
    IO.Process.output {cmd := "lake", args := #["env", "lean", "-D", "Elab.async=false", "--stdin", opts.input]} (some input)
  catch _ => return ← error "failed to launch the pinned Lean frontend through Lake"
  if result.exitCode != 0 || !compiling then
    (← IO.getStdout).putStr result.stdout
    (← IO.getStderr).putStr result.stderr
    return result.exitCode
  -- A separate successful full frontend pass is required before a command may write artifacts.
  -- Lean reports asynchronous earlier errors only when the frontend finishes.
  let command := (if opts.compactAdapter then "#nightlean_compile_compact " else "#nightlean_compile ") ++
    (Lean.toJson opts.output).compress
  let compileInput := "import Nightlean.Compiler " ++ source ++ "\n" ++ command ++ "\n"
  let result ← try
    IO.Process.output {cmd := "lake", args := #["env", "lean", "-D", "Elab.async=false", "--stdin", opts.input]} (some compileInput)
  catch _ => return ← error "failed to launch the pinned Lean compiler through Lake"
  (← IO.getStdout).putStr result.stdout
  (← IO.getStderr).putStr result.stderr
  return result.exitCode

def run (args : List String) : IO UInt32 := do
  match args with
  | [] | ["--help"] | ["-h"] =>
    IO.println usage
    return 0
  | ["--version"] =>
    IO.println s!"Nightlean {version} (Lean {Lean.versionString})"
    return 0
  | ["profiles"] =>
    IO.println "midnight-ledger-9 profiles/midnight-ledger-9.json source-baseline-unqualified"
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

end Nightlean.Cli
