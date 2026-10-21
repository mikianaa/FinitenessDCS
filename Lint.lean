import FinitenessDCS

/-!
# Lint and axiom checks

`lake build Lint` runs Mathlib's environment linters over the whole development and
checks that no declaration in `FinitenessDCS.*` depends on an axiom beyond Lean's
standard three (`propext`, `Classical.choice`, `Quot.sound`).  The latter rules out
both `sorry` (`sorryAx`) and `native_decide`.  CI builds this module on every push.
-/

#lint in FinitenessDCS

#print axioms DCS.main_dcs
#print axioms DCS.finiteness_main
#print axioms DCS.modulus_dvd_max
#print axioms DCS.cell_inequality
#print axioms DCS.cell_inequality_two_level
#print axioms DCS.divisor_sum_ineq

-- Fail the build unless every declaration of the project uses only the standard axioms.
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked := 0
  let mut bad : Array (Name × Array Name) := #[]
  for (c, _) in env.constants.map₁.toList do
    if c.isInternal then continue
    match env.getModuleIdxFor? c with
    | some idx =>
      if (mods[idx.toNat]!).toString.startsWith "FinitenessDCS" then
        checked := checked + 1
        let axs ← collectAxioms c
        let extra := axs.filter (fun a => !allowed.contains a)
        if !extra.isEmpty then bad := bad.push (c, extra)
    | none => pure ()
  if bad.isEmpty then
    logInfo m!"axiom check passed: {checked} declarations use only {allowed}"
  else
    for (c, axs) in bad.qsort (fun a b => a.1.toString < b.1.toString) do
      logError m!"{c} depends on non-standard axioms: {axs}"
    throwError "axiom check failed for {bad.size} declaration(s)"
