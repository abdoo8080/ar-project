import Lake
open Lake DSL

package smtArray {
  -- add package configuration options here
}

lean_lib SmtArray {
  -- add library configuration options here
}

@[default_target]
lean_exe array {
  root := `Main
}
