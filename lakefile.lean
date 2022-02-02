import Lake
open System Lake DSL

package ClausalExtraction where
  srcDir := "lib"
  libRoots := #[`ClausalExtraction]
  -- specify the lib as an additional target
  --moreLinkArgs := #["-Xlinker", "--error-limit=0"]