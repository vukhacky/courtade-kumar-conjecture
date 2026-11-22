import CK
import CK.PaperStatement
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean Elab Command

/- Check the transitive axiom dependencies of declarations imported from CK modules. -/
run_cmd do
  let env ← getEnv
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  let mut declarations : Nat := 0
  for (name, _) in env.constants.toList do
    let some origin := env.getModuleIdxFor? name |>.bind (env.header.modules[·]?) | continue
    if !Name.isPrefixOf `CK origin.module then continue
    declarations := declarations + 1
    let axioms ← collectAxioms name
    let unexpected := axioms.filter (fun axiomName => !allowed.contains axiomName)
    unless unexpected.isEmpty do
      throwError "{name} depends on disallowed axioms: {unexpected}"
  logInfo m!"Checked transitive axioms of {declarations} CK declarations."

#print axioms CK.main
#print axioms CK.functionalMain
#print axioms CK.mutualInformation_le_binaryEntropy
#print axioms CK.mutualInformation_le_signedDictator
#print axioms CK.randomMutualInformation_le_binaryEntropy_independent_flips
#print axioms CK.Paper.stoc_main
