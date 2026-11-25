import Lean.CoreM
import Lean.Replay
import Lean.Util.FoldConsts
import Lean.Compiler.Old
open Lean

unsafe def replayProjectModule (module : Name) : IO Nat := do
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"Missing module: {module}"
  let mut files := #[mFile]
  let server := OLeanLevel.server.adjustFileName mFile
  unless (← server.pathExists) do
    throw <| IO.userError s!"Missing server module data: {module}"
  files := files.push server
  let priv := OLeanLevel.private.adjustFileName mFile
  unless (← priv.pathExists) do
    throw <| IO.userError s!"Missing private proof bodies: {module}"
  files := files.push priv
  let parts ← readModuleDataParts files
  if h : parts.size = 0 then throw <| IO.userError "No module data" else
  let (mod, _) := parts[0]
  let (_, state) ← importModulesCore mod.imports |>.run
  let env ← finalizeImport state mod.imports {} 0 false false (isModule := true)
  let mut allConstants : Std.HashMap Name ConstantInfo := {}
  for name in parts[parts.size - 1].1.constNames, ci in parts[parts.size - 1].1.constants do
    allConstants := allConstants.insert name ci
  let mut constants : Std.HashMap Name ConstantInfo := {}
  for (name, ci) in allConstants.toList do
    if ci.isUnsafe || ci.isPartial then
      let some parent := Compiler.isUnsafeRecName? name
        | throw <| IO.userError s!"Non-compiler unsafe/partial project constant: {name}"
      let some original := allConstants[parent]?
        | throw <| IO.userError s!"Missing safe parent for compiler artifact: {name}"
      match original with
      | .defnInfo info =>
        unless info.safety == .safe do
          throw <| IO.userError s!"Non-safe definition parent for compiler artifact: {name}"
      | _ => throw <| IO.userError s!"Non-definition parent for compiler artifact: {name}"
      if (env.find? name).isSome then
        throw <| IO.userError s!"Skipped local compiler artifact already present in imports: {name}"
      IO.println s!"SKIP_COMPILER_RECURSION_ARTIFACT {name} safe_parent={parent}"
    else
      constants := constants.insert name ci
  let result ← env.replay constants
  result.freeRegions
  return constants.size

unsafe def moduleConstants (module : Name) : IO (Array ConstantInfo) := do
  let file ← findOLean module
  let mut files := #[file]
  let server := OLeanLevel.server.adjustFileName file
  unless (← server.pathExists) do
    throw <| IO.userError s!"Missing server module data: {module}"
  files := files.push server
  let priv := OLeanLevel.private.adjustFileName file
  unless (← priv.pathExists) do
    throw <| IO.userError s!"Missing private proof bodies: {module}"
  files := files.push priv
  let parts ← readModuleDataParts files
  if h : parts.size = 0 then throw <| IO.userError "No module data" else
  return parts[parts.size - 1].1.constants

partial def proofPath (constants : Std.HashMap Name ConstantInfo)
    (root target : Name) : Option (List Name) := Id.run do
  let mut pending : List (List Name) := [[root]]
  let mut seen : Std.HashSet Name := {}
  while !pending.isEmpty do
    let path := pending.head!
    pending := pending.tail!
    let name := path.head!
    if name == target then return some path.reverse
    if seen.contains name then continue
    seen := seen.insert name
    if let some ci := constants[name]? then
      if let some value := ci.value? (allowOpaque := true) then
        for dep in value.getUsedConstants do
          if constants.contains dep then pending := (dep :: path) :: pending
  return none

unsafe def main (args : List String) : IO UInt32 := do
  if args.isEmpty then throw <| IO.userError "Supply the production module list"
  initSearchPath (← findSysroot)
  let mut total := 0
  for name in args do
    let count ← replayProjectModule name.toName
    total := total + count
    IO.println s!"REPLAY_OK {name} {count}"
    (← IO.getStdout).flush
  let mut constants : Std.HashMap Name ConstantInfo := {}
  for name in args do
    for ci in ← moduleConstants name.toName do
      constants := constants.insert ci.name ci
  for (root, target) in [("ClockBarrier.Euler.general_clock_continuation", "ClockBarrier.Analysis.exists_positive_power_comparison"), ("ClockBarrier.Euler.axis_clock_barrier", "ClockBarrier.Analysis.exists_positive_power_comparison"), ("ClockBarrier.Euler.smallest_singularValue_evolution", "ClockBarrier.Analysis.spectral_gap_square_completion"), ("ClockBarrier.Euler.local_axis_coherence", "ClockBarrier.Geometry.fderiv_angular_generator_of_rotation"), ("ClockBarrier.Euler.general_driver_bound", "ClockBarrier.Euler.classical_euler_on.directional_initial_increment_bound"), ("ClockBarrier.Euler.general_driver_bound", "ClockBarrier.Analysis.integral_abs_add_le_of_bounds"), ("ClockBarrier.Euler.general_driver_bound", "ClockBarrier.Analysis.directional_strain_kernel_add"), ("ClockBarrier.Euler.axis_clock_barrier", "ClockBarrier.Euler.classical_euler_on.axis_strain_cylindrical_cauchy"), ("ClockBarrier.Euler.axis_clock_barrier", "ClockBarrier.Euler.classical_euler_on.deriv_axis_eq_smooth_near_add_far_of_cylindrical"), ("ClockBarrier.Euler.general_clock_continuation", "ClockBarrier.Analysis.le_linear_solution_of_right_deriv")] do
    let some path := proofPath constants root.toName target.toName
      | throw <| IO.userError s!"Missing compiled-proof route: {root} -> {target}"
    IO.println s!"PROOF_ROUTE_OK {String.intercalate " -> " (path.map toString)}"
  for (root, target) in [("ClockBarrier.Euler.smallest_singularValue_evolution", "ClockBarrier.Analysis.hasDerivWithinAt_sInf_range_of_minimizer"), ("ClockBarrier.Euler.local_axis_coherence", "ClockBarrier.Geometry.radius_bounds_of_halfTurn"), ("ClockBarrier.Euler.general_driver_bound", "ClockBarrier.Euler.classical_euler_on.initial_increment_lintegral_bound"), ("ClockBarrier.Euler.axis_clock_barrier", "ClockBarrier.Euler.classical_euler_on.deriv_axis_eq_smooth_near_add_far"), ("ClockBarrier.Euler.general_clock_continuation", "ClockBarrier.Analysis.exp_neg_integral_le_of_supercritical_power_deriv_ge"), ("ClockBarrier.Euler.axis_clock_barrier", "ClockBarrier.Analysis.exp_neg_integral_le_of_supercritical_power_deriv_ge")] do
    if (proofPath constants root.toName target.toName).isSome then
      throw <| IO.userError s!"Old alternate route remains consumed: {root} -> {target}"
    IO.println s!"OLD_ROUTE_ABSENT {root} -> {target}"
  IO.println s!"KERNEL_REPLAY_OK modules={args.length} constants={total}"
  return 0
