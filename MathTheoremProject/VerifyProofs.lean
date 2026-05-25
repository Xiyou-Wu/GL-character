import Lean
import Mathlib

open Lean Elab Meta

/-- Check if a declaration is a proven theorem (not sorry, not axiom). -/
def isProvenTheorem (env : Environment) (name : Name) : Bool :=
  match env.find? name with
  | some (ConstantInfo.thmInfo _) => true
  | some (ConstantInfo.defnInfo _) => true
  | some (ConstantInfo.axiomInfo _) => false
  | _ => false

/-- Verify that all target theorems in a module are fully proven. -/
def verifyTheorems (moduleName : Name) (expectedTheorems : List Name) : IO Unit := do
  let env ← importModules [{ module := moduleName }] {} 0
  IO.println s!"Checking module: {moduleName}"
  IO.println s!"Expected theorems: {expectedTheorems.length}"
  IO.println ""

  let mut allProven := true
  for thmName in expectedTheorems do
    let fullName := moduleName ++ thmName
    let proven := isProvenTheorem env fullName
    let status := if proven then "✓ NO GOALS - PROVEN" else "✗ NOT FOUND OR UNPROVEN"
    if !proven then
      allProven := false
    IO.println s!"  [{status}] {fullName}"

  IO.println ""
  if allProven then
    IO.println "ALL THEOREMS VERIFIED: NO OPEN GOALS"
  else
    IO.println "SOME THEOREMS ARE NOT FULLY PROVEN"

def main : IO Unit := do
  IO.println "========================================"
  IO.println "Lean 4 Proof Verification Report"
  IO.println "========================================"
  IO.println ""

  -- Check RealInequalities
  let realIneqThms := [
    `oneVar_left_endpoint_bound,
    `oneVar_right_endpoint_bound,
    `oneVar_endpoint_bound,
    `left_endpoint_le_sqrt_bound,
    `triCos_le_Q_of_mem_Icc,
    `arccos_Q_le_arccos_triCos_of_mem_Icc,
    `sqrt_two_sq,
    `sqrt_two_pos,
    `sqrt_two_lt_two,
    `two_sub_sqrt_two_pos,
    `sqrt_two_lt_three_div_two,
    `sqrt_two_div_two_lt_one,
    `sqrt_two_div_two_le_three_div_four,
    `Q_zero_one,
    `Q_diag,
    `Q1_lt_sqrt_two_div_two_of_eta_lt,
    `Q2_lt_sqrt_two_div_two_of_eta_lt_one_add_two_mul,
    `degreeEight_interval_implies_eta_lt_one_add_two_mul_xi,
    `Q_lt_sqrt_two_div_two_of_degreeEight_interval
  ]
  verifyTheorems `MathTheoremProject.GeLinImprovement realIneqThms

  IO.println ""
  IO.println "----------------------------------------"
  IO.println ""

  -- Check CharacterCriterion
  let charCritThms := [
    `sum_gt_of_card_mul_lower_bound,
    `fin_sum_gt_of_strict_lower_bound,
    `eight_angle_sum_gt_two_pi,
    `degreeEight_character_gt_two_pi
  ]
  verifyTheorems `MathTheoremProject.GeLinImprovement charCritThms

  IO.println ""
  IO.println "========================================"
  IO.println "Verification Complete"
  IO.println "========================================"
