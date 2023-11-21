import Lake

open Lake DSL

package render {
  -- add package configuration options here
}

lean_lib Render {
  -- add library configuration options here
}

@[default_target]
lean_exe render {
  root := `Main
}
