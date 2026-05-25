import Mathlib
import ProbabilityCharacter.Basic

/-! # Pointwise degree criteria for hyperbolic combinatorial Ricci flow

This file formalizes the two pointwise degree criteria from the blueprint:

1. **Constant weight criterion** (Corollary 1): If Phi is constant and every vertex
   has degree at least 7, then the hyperbolic combinatorial Ricci flow converges
   exponentially.  The proof reduces to the numerical inequality
   `7 * pi / 3 > 2 * pi`.

2. **Arbitrary weight criterion** (Corollary 2): If Phi is arbitrary in `[0, pi/2]`
   and every vertex has degree at least 9, then the flow converges exponentially.
   The proof uses the Ge--Lin angle estimate `L_i >= d_i * arccos(3/4)` and the
   numerical inequality `9 * arccos(3/4) > 2 * pi`.

Both corollaries are obtained by combining the pointwise lower bound on the
character `L_i` with `pointwise_criterion_implies_average_criterion` from
`ProbabilityCharacter.Basic`.
-/

namespace ProbabilityCharacter

open scoped BigOperators

noncomputable section

variable {V : Type*}

-- ---------------------------------------------------------------------------
-- Numerical lemmas
-- ---------------------------------------------------------------------------

/-- The constant-weight degree bound gives `7*pi/3 > 2*pi`. -/
lemma seven_pi_div_three_gt_two_pi : 7 * Real.pi / 3 > 2 * Real.pi := by
  linarith [Real.pi_pos]

/-- `cos(2*pi/9) > 3/4`, proved via the triple-angle identity.

    The polynomial `f(x) = 4x^3 - 3x + 1/2` has `f(cos(2*pi/9)) = 0` and is strictly
    increasing on `[1/2, 1]`.  Since `f(3/4) = -1/16 < 0`, we obtain
    `cos(2*pi/9) > 3/4`. -/
lemma cos_two_pi_div_nine_gt_three_div_four : Real.cos (2 * Real.pi / 9) > (3 / 4 : ℝ) := by
  have h3 : Real.cos (2 * Real.pi / 3) = 4 * (Real.cos (2 * Real.pi / 9))^3
      - 3 * (Real.cos (2 * Real.pi / 9)) := by
    rw [← Real.cos_three_mul]
    ring_nf
  have h4 : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
    have h5 : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
    rw [h5, Real.cos_pi_sub]
    norm_num
  have h8 : 0 < Real.cos (2 * Real.pi / 9) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
  have hcos1 : Real.cos (2 * Real.pi / 9) ≤ 1 := Real.cos_le_one _
  have h_eq : 4 * (Real.cos (2 * Real.pi / 9))^3 - 3 * (Real.cos (2 * Real.pi / 9)) + 1 / 2 = 0 := by
    linarith [h3, h4]
  have hf34 : 4 * (3 / 4 : ℝ)^3 - 3 * (3 / 4 : ℝ) + 1 / 2 = -1 / 16 := by norm_num
  have hf_cos : 4 * (Real.cos (2 * Real.pi / 9))^3 - 3 * (Real.cos (2 * Real.pi / 9)) + 1 / 2
      > 4 * (3 / 4 : ℝ)^3 - 3 * (3 / 4 : ℝ) + 1 / 2 := by
    linarith [h_eq, hf34]
  have h9 : Real.cos (2 * Real.pi / 9) > 1 / 2 := by
    have h10 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
    have h11 : 2 * Real.pi / 9 < Real.pi / 3 := by linarith [Real.pi_pos]
    have h12 : Real.cos (2 * Real.pi / 9) > Real.cos (Real.pi / 3) := by
      apply Real.cos_lt_cos_of_nonneg_of_le_pi
      · linarith [Real.pi_pos]
      · linarith [Real.pi_pos]
      · linarith [Real.pi_pos]
    linarith [h10, h12]
  by_contra h
  push Not at h
  have h10 : Real.cos (2 * Real.pi / 9) ≤ 3 / 4 := by linarith
  have h12 : (Real.cos (2 * Real.pi / 9) - 3 / 4)
      * (4 * (Real.cos (2 * Real.pi / 9)^2 + Real.cos (2 * Real.pi / 9) * (3 / 4) + (3 / 4)^2) - 3)
      > 0 := by
    have h13 : 4 * (Real.cos (2 * Real.pi / 9))^3 - 3 * (Real.cos (2 * Real.pi / 9)) + 1 / 2
        - (4 * (3 / 4 : ℝ)^3 - 3 * (3 / 4 : ℝ) + 1 / 2) > 0 := by
      linarith [hf_cos]
    have h14 : 4 * (Real.cos (2 * Real.pi / 9))^3 - 3 * (Real.cos (2 * Real.pi / 9)) + 1 / 2
        - (4 * (3 / 4 : ℝ)^3 - 3 * (3 / 4 : ℝ) + 1 / 2)
        = (Real.cos (2 * Real.pi / 9) - 3 / 4)
          * (4 * (Real.cos (2 * Real.pi / 9)^2 + Real.cos (2 * Real.pi / 9) * (3 / 4) + (3 / 4)^2) - 3) := by
      ring
    linarith [h13, h14]
  have h15 : 4 * (Real.cos (2 * Real.pi / 9)^2 + Real.cos (2 * Real.pi / 9) * (3 / 4) + (3 / 4)^2) - 3
      > 0 := by
    nlinarith [sq_nonneg (Real.cos (2 * Real.pi / 9) - 3 / 4),
      sq_nonneg (Real.cos (2 * Real.pi / 9) + 3 / 4),
      sq_nonneg (Real.cos (2 * Real.pi / 9) - 1), h9]
  have h16 : Real.cos (2 * Real.pi / 9) - 3 / 4 > 0 := by
    nlinarith [h12, h15]
  linarith [h16, h10]

/-- `9 * arccos(3/4) > 2*pi`, derived from `cos(2*pi/9) > 3/4` and the strict
    antitonicity of `arccos`. -/
lemma nine_arccos_three_div_four_gt_two_pi : 9 * Real.arccos (3 / 4 : ℝ) > 2 * Real.pi := by
  have h1 : Real.arccos (3 / 4 : ℝ) > 2 * Real.pi / 9 := by
    have h2 : Real.cos (2 * Real.pi / 9) > (3 / 4 : ℝ) := cos_two_pi_div_nine_gt_three_div_four
    have hcos1 : Real.cos (2 * Real.pi / 9) ≤ 1 := Real.cos_le_one _
    have h13 : Real.arccos (Real.cos (2 * Real.pi / 9)) < Real.arccos (3 / 4 : ℝ) := by
      apply Real.arccos_lt_arccos
      · norm_num
      · linarith
      · exact hcos1
    have h14 : Real.arccos (Real.cos (2 * Real.pi / 9)) = 2 * Real.pi / 9 := by
      apply Real.arccos_cos
      · linarith [Real.pi_pos]
      · linarith [Real.pi_pos]
    linarith
  linarith [Real.pi_pos]

-- ---------------------------------------------------------------------------
-- Degree criteria
-- ---------------------------------------------------------------------------

variable (degree : V → ℕ)

/-- **Corollary 1** (constant weight, pointwise degree criterion).

    When the weight `Phi` is constant (`= pi/3` per face), the vertex character is
    `L_i = pi * d_i / 3`.  If every vertex has degree at least 7, then
    `L_i >= 7*pi/3 > 2*pi` for all `i`, so the pointwise criterion holds and the
    hyperbolic combinatorial Ricci flow converges exponentially. -/
theorem pointwise_degree_criterion_constant_weight
    (L : V → ℝ) (Delta : Finset V → ℝ)
    (hL : ∀ i, L i = Real.pi * (degree i : ℝ) / 3)
    (hdeg : ∀ i, 7 ≤ degree i)
    (hDelta : ∀ I, 0 ≤ Delta I) :
    ∀ I : Finset V, I.Nonempty → 2 * Real.pi < correctedAverage L Delta I := by
  have hLi : ∀ i, 2 * Real.pi < L i := by
    intro i
    have h1 : L i = Real.pi * (degree i : ℝ) / 3 := hL i
    have h2 : 7 ≤ degree i := hdeg i
    have h3 : (7 : ℝ) ≤ (degree i : ℝ) := by exact_mod_cast h2
    have h4 : Real.pi * (7 : ℝ) / 3 ≤ Real.pi * (degree i : ℝ) / 3 := by
      have h7 : (7 : ℝ) ≤ (degree i : ℝ) := by exact_mod_cast h2
      have h8 : Real.pi * (7 : ℝ) ≤ Real.pi * (degree i : ℝ) := by
        apply (mul_le_mul_iff_of_pos_left Real.pi_pos).mpr
        linarith
      linarith
    have h5 : 2 * Real.pi < Real.pi * (7 : ℝ) / 3 := by
      have h6 : 2 * Real.pi < 7 * Real.pi / 3 := seven_pi_div_three_gt_two_pi
      linarith
    linarith [h1, h4, h5]
  exact pointwise_criterion_implies_average_criterion L Delta hLi hDelta

/-- **Corollary 2** (arbitrary weight, pointwise degree criterion).

    For arbitrary weights `Phi ∈ [0, pi/2]`, the Ge--Lin angle estimate gives
    `L_i >= d_i * arccos(3/4)`.  If every vertex has degree at least 9, then
    `L_i >= 9 * arccos(3/4) > 2*pi` for all `i`, so the pointwise criterion holds
    and the flow converges exponentially. -/
theorem pointwise_degree_criterion_arbitrary_weight
    (L : V → ℝ) (Delta : Finset V → ℝ)
    (hL : ∀ i, L i ≥ (degree i : ℝ) * Real.arccos (3 / 4))
    (hdeg : ∀ i, 9 ≤ degree i)
    (hDelta : ∀ I, 0 ≤ Delta I) :
    ∀ I : Finset V, I.Nonempty → 2 * Real.pi < correctedAverage L Delta I := by
  have hLi : ∀ i, 2 * Real.pi < L i := by
    intro i
    have h1 : (degree i : ℝ) * Real.arccos (3 / 4) ≤ L i := hL i
    have h2 : 9 ≤ degree i := hdeg i
    have h3 : (9 : ℝ) ≤ (degree i : ℝ) := by exact_mod_cast h2
    have h4 : (9 : ℝ) * Real.arccos (3 / 4) ≤ (degree i : ℝ) * Real.arccos (3 / 4) := by
      apply mul_le_mul_of_nonneg_right
      · linarith
      · apply Real.arccos_nonneg
    have h5 : 2 * Real.pi < (9 : ℝ) * Real.arccos (3 / 4) := by
      have h6 : 2 * Real.pi < 9 * Real.arccos (3 / 4) := nine_arccos_three_div_four_gt_two_pi
      linarith
    linarith [h1, h4, h5]
  exact pointwise_criterion_implies_average_criterion L Delta hLi hDelta

end

end ProbabilityCharacter
