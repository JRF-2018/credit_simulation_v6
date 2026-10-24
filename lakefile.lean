import Lake
open Lake DSL

package credit_simulation_v6

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.1"

@[default_target]
lean_lib CreditV6
