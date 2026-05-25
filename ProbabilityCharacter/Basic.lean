import Mathlib

/-!
# Algebraic helpers for the average character criterion

The geometric input in the note is the Chow--Luo obstruction identity. This
file records Lean-checked algebraic consequences of that identity. The
hyperbolic circle-packing existence and convergence theorems are intentionally
kept outside this file as external geometric inputs.
-/

namespace ProbabilityCharacter

open scoped BigOperators

noncomputable section

variable {V : Type*}

/-- Boundary-corrected average character of a finite vertex set. -/
def correctedAverage (L : V -> ℝ) (Delta : Finset V -> ℝ) (I : Finset V) : ℝ :=
  ((∑ i ∈ I, L i) + Delta I) / (I.card : ℝ)

/--
The Chow--Luo obstruction identity is equivalent to writing the obstruction as
cardinality times the corrected average surplus.
-/
theorem obstruction_eq_card_mul_surplus
    (L : V -> ℝ) (Delta B : Finset V -> ℝ) {I : Finset V} (hI : I.Nonempty)
    (hB : B I = (∑ i ∈ I, L i) - 2 * Real.pi * (I.card : ℝ) + Delta I) :
    B I = (I.card : ℝ) * (correctedAverage L Delta I - 2 * Real.pi) := by
  have hcard : (I.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hI)
  rw [hB, correctedAverage]
  field_simp [hcard]
  ring

/--
For a nonempty vertex set, positivity of the obstruction is the same as the
corrected average character being larger than `2 * Real.pi`.
-/
theorem obstruction_pos_iff_correctedAverage_gt
    (L : V -> ℝ) (Delta B : Finset V -> ℝ) {I : Finset V} (hI : I.Nonempty)
    (hB : B I = (I.card : ℝ) * (correctedAverage L Delta I - 2 * Real.pi)) :
    0 < B I ↔ 2 * Real.pi < correctedAverage L Delta I := by
  have hcard_pos : 0 < (I.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr hI)
  rw [hB]
  constructor
  · intro h
    have hsurplus : 0 < correctedAverage L Delta I - 2 * Real.pi :=
      pos_of_mul_pos_right h (le_of_lt hcard_pos)
    linarith
  · intro h
    have hsurplus : 0 < correctedAverage L Delta I - 2 * Real.pi := by
      linarith
    exact mul_pos hcard_pos hsurplus

/-- The corrected average inequality implies positivity of the obstruction. -/
theorem obstruction_pos_of_correctedAverage_gt
    (L : V -> ℝ) (Delta B : Finset V -> ℝ) {I : Finset V} (hI : I.Nonempty)
    (hB : B I = (I.card : ℝ) * (correctedAverage L Delta I - 2 * Real.pi))
    (hac : 2 * Real.pi < correctedAverage L Delta I) :
    0 < B I :=
  (obstruction_pos_iff_correctedAverage_gt L Delta B hI hB).2 hac

/--
If every vertex in a nonempty set has character larger than `2 * Real.pi`, and
the boundary correction is nonnegative, then that set satisfies the corrected
average inequality.
-/
theorem pointwise_gt_two_pi_correctedAverage_gt
    (L : V -> ℝ) (Delta : Finset V -> ℝ) {I : Finset V} (hI : I.Nonempty)
    (hL : ∀ i ∈ I, 2 * Real.pi < L i) (hDelta : 0 ≤ Delta I) :
    2 * Real.pi < correctedAverage L Delta I := by
  have hsum_const :
      (∑ _i ∈ I, (2 * Real.pi : ℝ)) = (I.card : ℝ) * (2 * Real.pi) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hsum_lt : (I.card : ℝ) * (2 * Real.pi) < ∑ i ∈ I, L i := by
    rw [← hsum_const]
    exact Finset.sum_lt_sum
      (fun i hi => le_of_lt (hL i hi))
      (let ⟨i, hi⟩ := hI; ⟨i, hi, hL i hi⟩)
  have hcard_pos : 0 < (I.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr hI)
  have htotal : (I.card : ℝ) * (2 * Real.pi) < (∑ i ∈ I, L i) + Delta I := by
    linarith
  rw [correctedAverage]
  apply (mul_lt_mul_iff_of_pos_right hcard_pos).mp
  have hcard_ne : (I.card : ℝ) ≠ 0 := ne_of_gt hcard_pos
  simpa [div_mul_cancel₀ _ hcard_ne, mul_comm] using htotal

/--
The pointwise Ge--Lin character criterion implies the boundary-corrected
average character criterion on every nonempty finite set.
-/
theorem pointwise_criterion_implies_average_criterion
    (L : V -> ℝ) (Delta : Finset V -> ℝ)
    (hL : ∀ i, 2 * Real.pi < L i) (hDelta : ∀ I, 0 ≤ Delta I) :
    ∀ I : Finset V, I.Nonempty -> 2 * Real.pi < correctedAverage L Delta I := by
  intro I hI
  exact pointwise_gt_two_pi_correctedAverage_gt L Delta hI
    (fun i _hi => hL i) (hDelta I)

/--
The average character formula converts the full-set average inequality into
negativity of the Euler characteristic.
-/
theorem eulerChar_neg_of_average_formula
    {card chi : ℝ} (hcard : 0 < card)
    (havg : 2 * Real.pi < 2 * Real.pi * (1 - chi / card)) :
    chi < 0 := by
  have htwopi : 0 < 2 * Real.pi := by positivity
  have hone : 1 < 1 - chi / card := by
    exact (lt_mul_iff_one_lt_right htwopi).mp havg
  have hdiv_neg : chi / card < 0 := by linarith
  exact ((div_neg_iff.mp hdiv_neg).resolve_left (by
    intro h
    exact not_lt_of_ge (le_of_lt hcard) h.2)).1

/--
Algebraic form of the constant-weight formula after substituting real-valued
cardinalities.
-/
theorem constant_weight_formula
    (degreeSum F1 F2 card : ℝ) (hcard : 0 < card) (phi : ℝ) :
    ((Real.pi / 3) * degreeSum + (Real.pi / 3) * F2 +
          (2 * Real.pi / 3 - phi) * F1) / card > 2 * Real.pi ↔
      degreeSum - 6 * card + F2 + (2 - 3 * phi / Real.pi) * F1 > 0 := by
  have hcard_ne : card ≠ 0 := ne_of_gt hcard
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hcard_ne, hpi]
  constructor <;> intro h <;> linarith

/--
The same constant-weight algebra with natural-number counts, matching the
cardinalities used in the blueprint statement.
-/
theorem constant_weight_formula_nat
    (degreeSum F1 F2 card : ℕ) (hcard : 0 < card) (phi : ℝ) :
    ((Real.pi / 3) * (degreeSum : ℝ) + (Real.pi / 3) * (F2 : ℝ) +
          (2 * Real.pi / 3 - phi) * (F1 : ℝ)) / (card : ℝ) > 2 * Real.pi ↔
      (degreeSum : ℝ) - 6 * (card : ℝ) + (F2 : ℝ) +
          (2 - 3 * phi / Real.pi) * (F1 : ℝ) > 0 := by
  exact constant_weight_formula
    (degreeSum : ℝ) (F1 : ℝ) (F2 : ℝ) (card : ℝ) (by exact_mod_cast hcard) phi

/--
Abstract version of the average character criterion. The conclusion `C` stands
for the external Chow--Luo existence, uniqueness, and flow convergence result.
Lean checks the reduction from the corrected average inequalities to the
Chow--Luo obstruction inequalities and the negative Euler characteristic.
-/
theorem average_character_criterion_skeleton
    (vertices : Finset V) (L : V -> ℝ) (Delta B : Finset V -> ℝ) (chi : ℝ)
    (C : Prop) (hvertices : vertices.Nonempty)
    (hglobal :
      correctedAverage L Delta vertices =
        2 * Real.pi * (1 - chi / (vertices.card : ℝ)))
    (hobstruction :
      ∀ I : Finset V, I.Nonempty -> I ≠ vertices ->
        B I = (I.card : ℝ) * (correctedAverage L Delta I - 2 * Real.pi))
    (hchow :
      chi < 0 ->
        (∀ I : Finset V, I.Nonempty -> I ≠ vertices -> 0 < B I) ->
        C)
    (hac : ∀ I : Finset V, I.Nonempty -> 2 * Real.pi < correctedAverage L Delta I) :
    C := by
  have hcard_pos : 0 < (vertices.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr hvertices)
  have hchi : chi < 0 := by
    apply eulerChar_neg_of_average_formula hcard_pos
    simpa [hglobal] using hac vertices hvertices
  apply hchow hchi
  intro I hI hproper
  exact obstruction_pos_of_correctedAverage_gt L Delta B hI
    (hobstruction I hI hproper) (hac I hI)

end

end ProbabilityCharacter
