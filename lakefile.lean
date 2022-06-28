import Lake
open Lake DSL

package render {
  -- add package configuration options here
}

lean_lib Render {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe render {
  root := `Main
}
