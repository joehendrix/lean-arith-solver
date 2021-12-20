import Lake
open System Lake DSL

package arithsolver where
  srcDir := "lib"
  libRoots := #[`ArithSolver]
  -- specify the lib as an additional target
  --moreLinkArgs := #["-Xlinker", "--error-limit=0"]