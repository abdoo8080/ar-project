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

@[default_target]
lean_exe lmt {
  root := `Main
}
