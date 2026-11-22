import Lake
open Lake DSL

package ck_formalization where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "c47f9ad906c5ec32a953f99911b446cd26dcc123"

@[default_target]
lean_lib CK
