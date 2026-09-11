import Medvedev
import Lean.Util.CollectAxioms

/-!
# Audit entry point

The command-line trust flag alone does not recheck imported proof bodies.
This file explicitly removes every project declaration from a copy of the
kernel environment and adds them back through `Kernel.Environment.addDeclCore`,
in dependency order. Inductives are checked again; their generated constructors
and recursors are compared with the originals. External library declarations
remain trusted imports. The separate dependency audit allows only Lean's
three standard classical axioms. Source-file inventory, module origin, and all
local declarations determine coverage; namespace prefixes alone are insufficient.
`MEDVEDEV_AUDIT_ROOT` defaults to the current directory. The driver imports this
entire module before calling `auditProject`; compiling this file alone does not
execute the replay. See DEEP_AUDIT.md and `scripts/run_audit.py`.
-/

#print axioms Medvedev.WangCode.correct
#print axioms Medvedev.tiling_iff_not_valid
#print axioms Medvedev.recognition
#print axioms Medvedev.Formula.pi01_characterization
#print axioms Medvedev.nonhalting_reduction
#print axioms Medvedev.Domino.MachineCode.domino_correct
#print axioms Medvedev.Domino.MachineCode.nonhalting_iff_valid
#print axioms Medvedev.Domino.ArithmeticBackground.no_torus
#print axioms Medvedev.Domino.windowHalts_iff_halts
#print axioms Medvedev.Domino.MachineCode.halts_iff_colored_periodic
#print axioms Medvedev.Domino.MachineCode.absolute_domino_correct
#print axioms Medvedev.Domino.Machine.halts_iff_absoluteHalts
#print axioms Medvedev.Domino.StandardTM.halts_iff
#print axioms Medvedev.Domino.StandardTM.nonhalting_iff_valid
#print axioms Medvedev.Domino.TM0Problem.compiler_correct
#print axioms Medvedev.rePred_not_inML
#print axioms Medvedev.not_computablePred_inML
#print axioms Medvedev.not_rePred_inML
#print axioms Medvedev.no_computable_bound

-- Access is needed only to remove constants from a temporary environment.
open private Lean.Kernel.Environment.mk Lean.Kernel.Environment.extensions
  Lean.Kernel.Environment.irBaseExts from Lean.Environment

set_option maxHeartbeats 0 in
def Medvedev.auditProject : Lean.Elab.Command.CommandElabM Unit := do
  let env ← Lean.getEnv
  let auditRoot : System.FilePath := (← IO.getEnv "MEDVEDEV_AUDIT_ROOT").getD "."
  unless (← (auditRoot / "Medvedev.lean").pathExists) &&
      (← (auditRoot / "Medvedev" / "Audit.lean").pathExists) do
    throwError "Audit source root is missing Medvedev.lean or Medvedev/Audit.lean: {auditRoot}"
  let mut projectModules : Array String := #[]
  for entry in ← auditRoot.readDir do
    if entry.path.extension == some "lean" then
      if let some stem := entry.path.fileStem then
        projectModules := projectModules.push stem
  let baseDepth := auditRoot.components.length
  for path in ← (auditRoot / "Medvedev").walkDir do
    if path.extension == some "lean" then
      let moduleName := String.intercalate "." ((path.withExtension "").components.drop baseDepth)
      projectModules := projectModules.push moduleName
  let isProject := fun (name : Lean.Name) =>
    name.toString.startsWith "Medvedev." || name.toString.startsWith "_private.Medvedev." ||
      match env.getModuleIdxFor? name with
      | some idx =>
        let mod := env.header.moduleNames[idx.toNat]!
        projectModules.contains mod.toString || mod == `Medvedev || mod.toString.startsWith "Medvedev."
      | none => true -- Current-file declarations have no imported-module index.
  let mut names : Array Lean.Name := #[]
  let mut theoremCount := 0
  for (name, info) in env.constants.toList do
    if isProject name then
      names := names.push name
      if info.isUnsafe then
        throwError "Unsafe project declaration is forbidden: {name}"
      match info with
      | .axiomInfo _ => throwError "Project axiom is forbidden: {name}"
      | .thmInfo _ => theoremCount := theoremCount + 1
      | _ => pure ()
  let collect : Lean.CollectAxioms.M Unit := names.forM Lean.CollectAxioms.collect
  let (_, result) := (collect.run env).run {}
  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
  for ax in result.axioms do
    unless allowed.contains ax do
      throwError "Unexpected axiom in the project dependency graph: {ax}"
  if names.isEmpty then throwError "No project declarations were audited"
  Lean.logInfo m!"AXIOM AUDIT PASSED: {names.size} project declarations, {theoremCount} theorems; axioms = {result.axioms}"

  -- Strip project constants, including ones outside the project's namespace.
  let mut retained : Lean.ConstMap := {}
  for (name, info) in env.constants.toList do
    unless isProject name do retained := retained.insert name info
  let original := env.toKernelEnv
  let mut checked := Lean.Kernel.Environment.mk retained original.quotInit original.diagnostics
    original.const2ModIdx (Lean.Kernel.Environment.extensions original)
    (Lean.Kernel.Environment.irBaseExts original) original.header
  let mut pending : Array Lean.Declaration := #[]
  let mut inductiveCount := 0
  let mut compilerHelperCount := 0
  for name in names do
    let some info := env.find? name | throwError "Missing project constant: {name}"
    match info with
    | .thmInfo v => pending := pending.push (.thmDecl v)
    | .defnInfo v =>
      if v.safety == .partial then
        -- Lean generates these recursive implementations from total definitions.
        -- They are opaque to kernel reduction; replay their bodies too.
        unless name.toString.endsWith "._unsafe_rec" && v.all == [name] do
          throwError "Unexpected partial declaration: {name}"
        pending := pending.push (.mutualDefnDecl [v])
        compilerHelperCount := compilerHelperCount + 1
      else pending := pending.push (.defnDecl v)
    | .opaqueInfo v => pending := pending.push (.opaqueDecl v)
    | .inductInfo v =>
      -- The present project has no nested inductives. Fail rather than silently
      -- weakening the replay if a future version introduces them.
      unless v.numNested == 0 do throwError "Nested inductive replay is unsupported: {name}"
      if v.all.head? == some name then
        let types ← v.all.mapM fun n => do
          let some (.inductInfo i) := env.find? n | throwError "Missing inductive: {n}"
          let ctors ← i.ctors.mapM fun c => do
            let some (.ctorInfo ci) := env.find? c | throwError "Missing constructor: {c}"
            pure ({ name := c, type := ci.type } : Lean.Constructor)
          pure ({ name := n, type := i.type, ctors } : Lean.InductiveType)
        pending := pending.push (.inductDecl v.levelParams v.numParams types false)
        inductiveCount := inductiveCount + 1
    | .ctorInfo _ | .recInfo _ => pure () -- Regenerated by the checked inductive declaration.
    | _ => throwError "Unsupported project declaration: {name}"

  let declarationCount := pending.size
  while !pending.isEmpty do
    let mut later : Array Lean.Declaration := #[]
    let mut progress := false
    for decl in pending do
      let dependencies : Array Lean.Name := Id.run <|
        decl.foldExprM (fun ns e => pure (ns ++ e.getUsedConstants)) #[]
      let ownNames := decl.getNames
      if dependencies.all (fun n => ownNames.contains n || (checked.find? n).isSome) then
        match checked.addDeclCore 0 decl none with
        | .ok next => checked := next
        | .error ex => throwError "Kernel replay failed for {decl.getTopLevelNames}:\n{ex.toMessageData (← Lean.getOptions)}"
        progress := true
      else later := later.push decl
    unless progress do
      throwError "Kernel replay has cyclic or missing dependencies: {later.map (·.getTopLevelNames)}"
    pending := later

  -- In particular, don't trust stored recursor reduction rules or constructor
  -- metadata merely because their parent inductive was accepted.
  for name in names do
    let some old := env.find? name | throwError "Missing original: {name}"
    let some fresh := checked.find? name | throwError "Project constant was not replayed: {name}"
    let same : Bool := match old, fresh with
      | .inductInfo a, .inductInfo b =>
        a.toConstantVal == b.toConstantVal && a.numParams == b.numParams &&
        a.numIndices == b.numIndices && a.all == b.all && a.ctors == b.ctors &&
        a.numNested == b.numNested && a.isRec == b.isRec &&
        a.isUnsafe == b.isUnsafe && a.isReflexive == b.isReflexive
      | .ctorInfo a, .ctorInfo b => a == b
      | .recInfo a, .recInfo b => a == b
      | .thmInfo a, .thmInfo b => a == b
      | .defnInfo a, .defnInfo b => a == b
      | .opaqueInfo a, .opaqueInfo b => a == b
      | _, _ => false
    unless same do throwError "Replayed declaration differs from stored original: {name}"
  Lean.logInfo m!"KERNEL REPLAY PASSED: {declarationCount} declaration groups, {inductiveCount} inductive groups, {compilerHelperCount} compiler helpers; all {names.size} project constants reproduced"
