import Lake
open Lake DSL

package extra

@[default_target]
lean_lib Extra

require std from git "https://github.com/leanprover/std4" @ "v4.3.0-rc2"
