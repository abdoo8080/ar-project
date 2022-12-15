import Lake

open Lake DSL

package LMT {
  -- add package configuration options here
}

lean_lib LMT {
  -- add library configuration options here
}

lean_lib Sexp {
  -- add library configuration options here
}

lean_exe generator {
  root := `Generator
}

lean_exe translator {
  root := `Translator
}

open System in
partial def readAllFiles (dir : FilePath) : IO (Array FilePath) := do
  let mut files := #[]
  for entry in (← FilePath.readDir dir) do
    if ← entry.path.isDir then
      files := (← readAllFiles entry.path) ++ files
    else
      files := files.push entry.path
  return files

open System in
/--
Run tests.
USAGE:
  lake run test
Run tests.
-/
script test do
  let lean ← getLean
  let files ← readAllFiles (FilePath.mk "Test")
  let mut tests : Array FilePath := #[]
  for file in files do
    if file.extension = some "lean" then
      tests := tests.push file
  let mut tasks := []
  for t in tests do
    tasks := (← IO.asTask (runTest lean t (← readThe Lake.Context))) :: tasks
  for task in tasks do
    let code ← IO.ofExcept task.get
    if code != 0 then
      return code
  return 0
where
  runTest (lean : FilePath) (test : FilePath) : ScriptM UInt32 := do
    IO.println s!"Start: {test}"
    let leanPath ← getAugmentedLeanPath
    -- Note: this only works on Unix since it needs the shared library `libLMT`
    -- to also load its transitive dependencies.
    let dynlib := (← findModule? `LMT).get!.dynlibFile
    let out ← IO.Process.output {
      cmd := lean.toString
      args := #[s!"--load-dynlib={dynlib}", test.toString]
      env := #[("LEAN_PATH", leanPath.toString)]
    }
    if !out.stderr.isEmpty || !out.stdout.isEmpty then
      IO.println s!"Failed: {test}"
      IO.println s!"Stderr:\n{out.stderr}"
      IO.println s!"Stdout:\n{out.stdout}"
      return 2
    IO.println s!"Passed: {test}"
    return 0

open System in
/--
Translate SMT tests.
USAGE:
  lake run translate
Translate SMT tests in `Test/SMT` directory.
-/
script translate do
  let tests ← readAllFiles ((FilePath.mk "Test").join "SMT")
  let mut tasks := []
  for t in tests do
    tasks := (← IO.asTask (runTest t)) :: tasks
  for task in tasks do
    let code ← IO.ofExcept task.get
    if code != 0 then
      return code
  return 0
where
  testNum (test : FilePath) := test.fileStem.get!.drop 4
  runTest (test : FilePath) : IO UInt32 := do
    IO.println s!"Translating: {test}"
    let out ← IO.Process.output {
      cmd := "lake"
      args := #["exe", "translator", test.toString]
    }
    if !out.stderr.isEmpty then
      IO.println s!"Failed: {test}"
      IO.println s!"Stderr:\n{out.stderr}"
      return 2
    IO.FS.writeFile (((FilePath.mk "Test").join "Lean").join s!"Test{testNum test}.lean") out.stdout
    IO.println s!"Done: {test}"
    return 0
