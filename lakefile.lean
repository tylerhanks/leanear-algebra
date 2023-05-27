import Lake
open Lake DSL

package «leanear-algebra» {
  -- add package configuration options here
}

lean_lib LeanearAlgebra {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe «leanear-algebra» {
  root := `Main
}
