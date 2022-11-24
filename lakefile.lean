import Lake
open Lake DSL

package A {
  -- add package configuration options here
}

lean_lib A {
  -- add library configuration options here
}

@[default_target]
lean_exe a {
  root := `Main
}
