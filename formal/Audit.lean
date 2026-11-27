import Lean
import Lean.Util.FoldConsts
import PureS

#print axioms UniformS.Numerical.universal_single_natural_io
#print axioms UniformS.Numerical.accepted_tree_origin
#print axioms UniformS.Numerical.universal_natural_io
#print axioms UniformS.Numerical.all_machine_tables
#print axioms UniformS.Numerical.unique_output
#print axioms UniformS.Numerical.tape_natural_io
#print axioms UniformS.Numerical.regular_domain
#print axioms UniformS.Numerical.physical_outputs
#print axioms UniformS.Numerical.decode_completed
#print axioms UniformS.Numerical.sigma_native
#print axioms UniformS.Numerical.active_block
#print axioms UniformS.Numerical.halt_stable
#print axioms UniformS.Numerical.size_exact
#print axioms UniformS.Archive.windows_exact
#print axioms UniformS.Archive.completed_ground
#print axioms UniformS.Archive.native_consumption
#print axioms UniformS.Separation.first_numeric_cutoff
#print axioms PureSFormal.Computation.CookSeedPassSourceReflection.exists_terminalRow_iff
#print axioms UniformS.Micro.universal_single_contractions
#print axioms UniformS.Micro.micro_block
#print axioms UniformS.Micro.micro_realizes
#print axioms UniformS.Micro.step_native
#print axioms UniformS.Micro.normal_exact
#print axioms UniformS.Output.binary_io
#print axioms UniformS.Output.any_bit_channel
#print axioms UniformS.Output.round_native
#print axioms UniformS.Certified.universal_selected_halting
#print axioms UniformS.Certified.all_terms_native
#print axioms UniformS.Certified.head_correct
#print axioms UniformS.Certified.all_program_queues
#print axioms UniformS.Certified.orbit_literal
#print axioms UniformS.BareMacro.selected_spec
#print axioms UniformS.Readback.tape_halts_iff_empty_bare_sample
#print axioms UniformS.exact_encoder_leaves
#print axioms UniformS.Bridge.tape_halts_iff_native_samples
#print axioms UniformS.physical_history_step
#print axioms UniformS.ground_history
#print axioms UniformS.ground_trace
#print axioms UniformS.macro_exact
#print axioms UniformS.Automaton.reports_normal
#print axioms UniformS.Automaton.oneStep_native
#print axioms UniformS.Automaton.parse_history
#print axioms UniformS.Automaton.seed_detector
#print axioms UniformS.Queue.sweep
#print axioms UniformS.Separation.combined_cutoff
#print axioms UniformS.copy_exact
#print axioms UniformS.trajectory_cost
#print axioms PureSFormal.Computation.DeterministicTapeCook.halts_iff_exists_fixedCookEmpty

set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let records := env.constants.toList.filterMap fun (name,info) => do
    let idx ← env.const2ModIdx[name]?
    let mod ← env.header.moduleNames[idx.toNat]?
    if !((`PureS).isPrefixOf mod) || !((`UniformS).isPrefixOf name) || name.isInternal then none
    else some (name,mod,info)
  for (name,mod,info) in records do
    let kind := match info with
      | .thmInfo _ => "theorem" | .defnInfo _ => "definition" | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor" | .recInfo _ => "recursor" | _ => "other"
    let axioms ← collectAxioms name
    let stmt ← liftTermElabM do return (← Meta.ppExpr info.type).pretty 180
    let deps := info.getUsedConstantsAsSet.toList.filter (fun n =>
      ((`UniformS).isPrefixOf n || (`PureSFormal).isPrefixOf n) && n != name)
    let row := Json.mkObj [("name",toJson name.toString),("module",toJson mod.toString),
      ("kind",toJson kind),("statement",toJson stmt),("axioms",toJson (axioms.map Name.toString)),
      ("direct_project_dependencies",toJson (deps.map Name.toString)),
      ("unsafe",toJson info.isUnsafe),("partial",toJson info.isPartial)]
    IO.println ("DECL " ++ row.compress)
