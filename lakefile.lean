import Lake
open Lake DSL

package responsibility_info_kernel where

require responsibility_os_kernel from git
  "https://github.com/GhostDriftTheory/responsibility-os-kernel.git" @
    "9b4e7d25572f3a1e114508bdf1a2d62349e83993"

lean_lib ResponsibilityInfoKernel

lean_lib GenericNoncommutativity
