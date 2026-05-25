import Mathlib
import ProbabilityCharacter.Basic
import ProbabilityCharacter.Combinatorics

/-! # Non-negativity of the correction term Δ_Φ(I)

This file proves that for every nonempty subset I ⊆ V, the correction term
Δ_Φ(I) is nonnegative.  The proof follows the blueprint exactly:

1. γ_out^f ≥ 0 because arccos has range [0, π].
2. For f ∈ F_1(I) with v_f the unique vertex in I and e_f = jk the opposite edge,
   we show γ_{v_f}^f ≤ π/2, and since Φ(e_f) ≤ π/2, we get
   π - Φ(e_f) - γ_{v_f}^f ≥ 0.

The key real inequality is that `triCos` is nonnegative when the inputs are
cosines of angles in [0, π/2].
-/

namespace ProbabilityCharacter

open scoped BigOperators
open Real

noncomputable section

-- ---------------------------------------------------------------------------
-- 0.  Inline triCos definition (from MathTheoremProject.GeLinImprovement)
-- ---------------------------------------------------------------------------

/-- The cosine term of one Euclidean unit packing angle. -/
def triCos (a b c : ℝ) : ℝ :=
  (1 + a + b - c) / (2 * Real.sqrt (1 + a) * Real.sqrt (1 + b))

-- ---------------------------------------------------------------------------
-- 1.  Real lemmas about triCos and arccos
-- ---------------------------------------------------------------------------

/-- When a, b, c are cosines of angles in [0, π/2], the triCos numerator is nonnegative.
    Specifically: 1 + a + b - c ≥ 0 because c ≤ 1 and a, b ≥ 0. -/
lemma triCos_numerator_nonneg {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : c ≤ 1) :
    0 ≤ 1 + a + b - c := by
  linarith

/-- When a, b > -1, the denominator of triCos is positive. -/
lemma triCos_denominator_pos {a b : ℝ} (ha : -1 < a) (hb : -1 < b) :
    0 < 2 * sqrt (1 + a) * sqrt (1 + b) := by
  have h1a : 0 < 1 + a := by linarith
  have h1b : 0 < 1 + b := by linarith
  positivity

/-- triCos is nonnegative when a, b ≥ 0 and c ≤ 1, with a, b > -1 for the denominator. -/
lemma triCos_nonneg {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : c ≤ 1) (ha1 : -1 < a) (hb1 : -1 < b) :
    0 ≤ triCos a b c := by
  unfold triCos
  apply div_nonneg
  · -- numerator
    exact triCos_numerator_nonneg ha hb hc
  · -- denominator
    exact le_of_lt (triCos_denominator_pos ha1 hb1)

/-- For angles in [0, π/2], cos is nonnegative. -/
lemma cos_nonneg_of_Icc {phi : ℝ} (hphi : phi ∈ Set.Icc 0 (π / 2)) : 0 ≤ cos phi := by
  have h1 : -(π / 2) ≤ phi := by linarith [hphi.1, Real.pi_pos]
  have h2 : phi ≤ π / 2 := hphi.2
  have h3 : phi ≤ π := by linarith [hphi.2, Real.pi_pos]
  apply cos_nonneg_of_mem_Icc
  constructor <;> linarith

/-- For phi in [0, π/2], cos phi > -1 (in fact cos phi ≥ 0). -/
lemma cos_gt_neg_one_of_Icc {phi : ℝ} (hphi : phi ∈ Set.Icc 0 (π / 2)) : -1 < cos phi := by
  have h1 : 0 ≤ cos phi := cos_nonneg_of_Icc hphi
  have h2 : cos phi ≠ -1 := by
    by_contra hcos
    have h3 : phi = π := by
      have h4 : cos phi = cos π := by rw [hcos]; exact Real.cos_pi.symm
      have h5 : phi ≥ 0 := hphi.1
      have h6 : phi ≤ π := by linarith [hphi.2, Real.pi_pos]
      have h7 : arccos (cos phi) = arccos (cos π) := by rw [h4]
      rw [Real.arccos_cos h5 h6, Real.arccos_cos (by linarith [Real.pi_pos]) (by linarith)] at h7
      linarith
    linarith [hphi.2, Real.pi_pos]
  linarith

/-- triCos ≤ 1 when a, b, c are cosines of angles in [0, π/2].
    This is equivalent to (1 + a + b - c)^2 ≤ 4(1+a)(1+b). -/
lemma triCos_le_one {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : c ≤ 1) (hc_nonneg : 0 ≤ c) :
    triCos a b c ≤ 1 := by
  unfold triCos
  have h1 : 0 < 1 + a := by linarith [ha]
  have h2 : 0 < 1 + b := by linarith [hb]
  have hden_pos : 0 < 2 * sqrt (1 + a) * sqrt (1 + b) := by
    have h1a : 0 < 1 + a := by linarith [ha]
    have h1b : 0 < 1 + b := by linarith [hb]
    positivity
  have hnum_nonneg : 0 ≤ 1 + a + b - c := by linarith [ha, hb, hc]
  -- We need to show (1 + a + b - c) / (2 * sqrt(1+a) * sqrt(1+b)) ≤ 1,
  -- i.e. 1 + a + b - c ≤ 2 * sqrt(1+a) * sqrt(1+b).
  -- Square both sides: (1 + a + b - c)^2 ≤ 4 * (1+a) * (1+b).
  have h6 : 1 + a + b - c ≤ 2 * sqrt (1 + a) * sqrt (1 + b) := by
    have h_sq : (1 + a + b - c) ^ 2 ≤ (2 * sqrt (1 + a) * sqrt (1 + b)) ^ 2 := by
      have hs1 : (sqrt (1 + a)) ^ 2 = 1 + a := Real.sq_sqrt (by linarith)
      have hs2 : (sqrt (1 + b)) ^ 2 = 1 + b := Real.sq_sqrt (by linarith)
      have h_eq : (2 * sqrt (1 + a) * sqrt (1 + b)) ^ 2 = 4 * (1 + a) * (1 + b) := by
        calc
          (2 * sqrt (1 + a) * sqrt (1 + b)) ^ 2
              = 4 * (sqrt (1 + a) ^ 2) * (sqrt (1 + b) ^ 2) := by ring
          _ = 4 * (1 + a) * (1 + b) := by rw [hs1, hs2]
      rw [h_eq]
      -- Expand: (1+a+b-c)^2 = 1 + a^2 + b^2 + c^2 + 2a + 2b - 2c + 2ab - 2ac - 2bc
      -- We need this ≤ 4(1+a)(1+b) = 4 + 4a + 4b + 4ab
      -- Rearrange: 0 ≤ 3 + 2a + 2b + 6c + 2ab + 2ac + 2bc - c^2 - a^2 - b^2
      -- Since a,b,c ∈ [0,1], all terms are bounded and the inequality holds.
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + 1 - c), sq_nonneg (b + 1 - c),
                sq_nonneg (c - 1), sq_nonneg (a - c), sq_nonneg (b - c),
                mul_nonneg ha hb, mul_nonneg ha hc_nonneg, mul_nonneg hb hc_nonneg,
                ha, hb, hc_nonneg, hc]
    have h_right_nonneg : 0 ≤ 2 * sqrt (1 + a) * sqrt (1 + b) := by
      exact le_of_lt hden_pos
    nlinarith [h_sq, hnum_nonneg, h_right_nonneg,
              Real.sqrt_nonneg (1 + a), Real.sqrt_nonneg (1 + b)]
  exact (div_le_one hden_pos).mpr h6

/-- For a face f = ijk with angles in [0, π/2], cos γ_i^f ≥ 0.
    This follows from triCos_nonneg. -/
lemma gamma_cos_nonneg
    {phi_ij phi_ik phi_jk : ℝ}
    (hij : phi_ij ∈ Set.Icc 0 (π / 2))
    (hik : phi_ik ∈ Set.Icc 0 (π / 2))
    (hjk : phi_jk ∈ Set.Icc 0 (π / 2)) :
    0 ≤ cos (arccos (triCos (cos phi_ij) (cos phi_ik) (cos phi_jk))) := by
  set a := cos phi_ij
  set b := cos phi_ik
  set c := cos phi_jk
  have ha_nonneg : 0 ≤ a := cos_nonneg_of_Icc hij
  have hb_nonneg : 0 ≤ b := cos_nonneg_of_Icc hik
  have hc_le_one : c ≤ 1 := cos_le_one phi_jk
  have hc_nonneg : 0 ≤ c := cos_nonneg_of_Icc hjk
  have ha1 : -1 < a := cos_gt_neg_one_of_Icc hij
  have hb1 : -1 < b := cos_gt_neg_one_of_Icc hik
  have h_triCos_nonneg : 0 ≤ triCos a b c :=
    triCos_nonneg ha_nonneg hb_nonneg hc_le_one ha1 hb1
  have h_triCos_le_one : triCos a b c ≤ 1 :=
    triCos_le_one ha_nonneg hb_nonneg hc_le_one hc_nonneg
  -- cos (arccos x) = x when x ∈ [-1, 1]
  rw [Real.cos_arccos (by linarith [h_triCos_nonneg]) (by linarith [h_triCos_le_one])]
  exact h_triCos_nonneg

-- Auxiliary lemma: triCos bounds for angles in [0, π/2]
private lemma triCos_bounds_of_Icc
    {phi_ij phi_ik phi_jk : ℝ}
    (hij : phi_ij ∈ Set.Icc 0 (π / 2))
    (hik : phi_ik ∈ Set.Icc 0 (π / 2))
    (hjk : phi_jk ∈ Set.Icc 0 (π / 2)) :
    let a := cos phi_ij; let b := cos phi_ik; let c := cos phi_jk
    0 ≤ triCos a b c ∧ triCos a b c ≤ 1 := by
  intro a b c
  have ha_nonneg : 0 ≤ a := cos_nonneg_of_Icc hij
  have hb_nonneg : 0 ≤ b := cos_nonneg_of_Icc hik
  have hc_le_one : c ≤ 1 := cos_le_one phi_jk
  have hc_nonneg : 0 ≤ c := cos_nonneg_of_Icc hjk
  have ha1 : -1 < a := cos_gt_neg_one_of_Icc hij
  have hb1 : -1 < b := cos_gt_neg_one_of_Icc hik
  constructor
  · exact triCos_nonneg ha_nonneg hb_nonneg hc_le_one ha1 hb1
  · exact triCos_le_one ha_nonneg hb_nonneg hc_le_one hc_nonneg

/-- The comparison angle γ is in [0, π/2] when all phi angles are in [0, π/2]. -/
lemma gamma_nonneg_and_le_pi_div_two
    {phi_ij phi_ik phi_jk : ℝ}
    (hij : phi_ij ∈ Set.Icc 0 (π / 2))
    (hik : phi_ik ∈ Set.Icc 0 (π / 2))
    (hjk : phi_jk ∈ Set.Icc 0 (π / 2)) :
    0 ≤ arccos (triCos (cos phi_ij) (cos phi_ik) (cos phi_jk)) ∧
    arccos (triCos (cos phi_ij) (cos phi_ik) (cos phi_jk)) ≤ π / 2 := by
  have hcos_nonneg : 0 ≤ cos (arccos (triCos (cos phi_ij) (cos phi_ik) (cos phi_jk))) :=
    gamma_cos_nonneg hij hik hjk
  constructor
  · -- 0 ≤ gamma
    exact Real.arccos_nonneg _
  · -- gamma ≤ π / 2
    rw [Real.arccos_le_pi_div_two]
    -- Need to show 0 ≤ triCos (...), which follows from hcos_nonneg after rewriting cos(arccos(x)) = x
    have h_eq : cos (arccos (triCos (cos phi_ij) (cos phi_ik) (cos phi_jk))) =
        triCos (cos phi_ij) (cos phi_ik) (cos phi_jk) := by
      have h := triCos_bounds_of_Icc hij hik hjk
      exact Real.cos_arccos (by linarith [h.1]) (by linarith [h.2])
    linarith [h_eq, hcos_nonneg]

/-- γ_i^f ≥ 0 for any valid face angles. -/
lemma gamma_nonneg
    {phi_ij phi_ik phi_jk : ℝ}
    (hij : phi_ij ∈ Set.Icc 0 (π / 2))
    (hik : phi_ik ∈ Set.Icc 0 (π / 2))
    (hjk : phi_jk ∈ Set.Icc 0 (π / 2)) :
    0 ≤ arccos (triCos (cos phi_ij) (cos phi_ik) (cos phi_jk)) := by
  exact (gamma_nonneg_and_le_pi_div_two hij hik hjk).1

/-- γ_i^f ≤ π/2 for any valid face angles. -/
lemma gamma_le_pi_div_two
    {phi_ij phi_ik phi_jk : ℝ}
    (hij : phi_ij ∈ Set.Icc 0 (π / 2))
    (hik : phi_ik ∈ Set.Icc 0 (π / 2))
    (hjk : phi_jk ∈ Set.Icc 0 (π / 2)) :
    arccos (triCos (cos phi_ij) (cos phi_ik) (cos phi_jk)) ≤ π / 2 := by
  exact (gamma_nonneg_and_le_pi_div_two hij hik hjk).2

-- ---------------------------------------------------------------------------
-- 2.  Non-negativity of individual correction terms
-- ---------------------------------------------------------------------------

/-- For an F2 face, γ_out^f ≥ 0 because arccos has range [0, π]. -/
lemma gamma_out_nonneg
    {phi_1 phi_2 phi_3 : ℝ}
    (h1 : phi_1 ∈ Set.Icc 0 (π / 2))
    (h2 : phi_2 ∈ Set.Icc 0 (π / 2))
    (h3 : phi_3 ∈ Set.Icc 0 (π / 2)) :
    0 ≤ arccos (triCos (cos phi_1) (cos phi_2) (cos phi_3)) := by
  exact gamma_nonneg h1 h2 h3

/-- For an F1 face with v_f in I and opposite edge e_f = jk:
    π - Φ(e_f) - γ_{v_f}^f ≥ 0 because Φ(e_f) ≤ π/2 and γ_{v_f}^f ≤ π/2. -/
lemma F1_term_nonneg
    {phi_jk phi_ij phi_ik : ℝ}
    (hjk : phi_jk ∈ Set.Icc 0 (π / 2))
    (hij : phi_ij ∈ Set.Icc 0 (π / 2))
    (hik : phi_ik ∈ Set.Icc 0 (π / 2)) :
    0 ≤ π - phi_jk - arccos (triCos (cos phi_ij) (cos phi_ik) (cos phi_jk)) := by
  have h1 : phi_jk ≤ π / 2 := hjk.2
  have h2 : arccos (triCos (cos phi_ij) (cos phi_ik) (cos phi_jk)) ≤ π / 2 :=
    gamma_le_pi_div_two hij hik hjk
  linarith [Real.pi_pos]

-- ---------------------------------------------------------------------------
-- 3.  Definition of Δ_Φ and the main theorem
-- ---------------------------------------------------------------------------

variable {V : Type*} [DecidableEq V]
variable (T : Combinatorics.TriangulationModel V)

/-- A weight function assigning to each edge an angle in [0, π/2]. -/
def IsValidWeight (Phi : Combinatorics.TriEdge V → ℝ) : Prop :=
  ∀ e, Phi e ∈ Set.Icc 0 (π / 2)

/-- The correction term Δ_Φ(I) for a subset I.

    We parameterize over functions that extract the geometric data from faces:
    - `gammaOutF2` gives γ_out^f for each f ∈ F2(I)
    - `phiEF1` gives Φ(e_f) for each f ∈ F1(I)
    - `gammaVF1` gives γ_{v_f}^f for each f ∈ F1(I)

    The non-negativity theorem assumes these functions produce values consistent
    with the geometric definitions. -/
def DeltaPhi
    (I : Finset V)
    (gammaOutF2 : Combinatorics.TriFace V → ℝ)
    (phiEF1 : Combinatorics.TriFace V → ℝ)
    (gammaVF1 : Combinatorics.TriFace V → ℝ) : ℝ :=
  ∑ f ∈ Combinatorics.TriangulationModel.F2 T I, gammaOutF2 f +
  ∑ f ∈ Combinatorics.TriangulationModel.F1 T I, (π - phiEF1 f - gammaVF1 f)

/-- The main theorem: Δ_Φ(I) ≥ 0 for every nonempty I ⊆ V,
    provided all the geometric terms come from valid angles in [0, π/2]. -/
theorem DeltaPhi_nonneg
    (I : Finset V)
    (gammaOutF2 : Combinatorics.TriFace V → ℝ)
    (phiEF1 : Combinatorics.TriFace V → ℝ)
    (gammaVF1 : Combinatorics.TriFace V → ℝ)
    (h_gammaOut_nonneg : ∀ f ∈ Combinatorics.TriangulationModel.F2 T I, 0 ≤ gammaOutF2 f)
    (h_F1_term_nonneg : ∀ f ∈ Combinatorics.TriangulationModel.F1 T I,
      0 ≤ π - phiEF1 f - gammaVF1 f) :
    0 ≤ DeltaPhi T I gammaOutF2 phiEF1 gammaVF1 := by
  unfold DeltaPhi
  have hsum1 : 0 ≤ ∑ f ∈ Combinatorics.TriangulationModel.F2 T I, gammaOutF2 f := by
    apply Finset.sum_nonneg
    intro f hf
    exact h_gammaOut_nonneg f hf
  have hsum2 : 0 ≤ ∑ f ∈ Combinatorics.TriangulationModel.F1 T I, (π - phiEF1 f - gammaVF1 f) := by
    apply Finset.sum_nonneg
    intro f hf
    exact h_F1_term_nonneg f hf
  linarith

/-- Concrete version: if gammaOutF2 values are actual comparison angles from
    valid face data, and F1 terms are π - phi - gamma with valid angles,
    then Δ_Φ(I) ≥ 0. -/
theorem DeltaPhi_nonneg_of_valid_angles
    (I : Finset V)
    (gammaOutF2 : Combinatorics.TriFace V → ℝ)
    (phiEF1 : Combinatorics.TriFace V → ℝ)
    (gammaVF1 : Combinatorics.TriFace V → ℝ)
    (h_gammaOut_valid : ∀ f ∈ Combinatorics.TriangulationModel.F2 T I,
      ∃ phi_1 phi_2 phi_3 : ℝ,
        phi_1 ∈ Set.Icc 0 (π / 2) ∧ phi_2 ∈ Set.Icc 0 (π / 2) ∧
        phi_3 ∈ Set.Icc 0 (π / 2) ∧
        gammaOutF2 f = arccos (triCos (cos phi_1) (cos phi_2) (cos phi_3)))
    (h_F1_valid : ∀ f ∈ Combinatorics.TriangulationModel.F1 T I,
      ∃ phi_jk phi_ij phi_ik : ℝ,
        phi_jk ∈ Set.Icc 0 (π / 2) ∧ phi_ij ∈ Set.Icc 0 (π / 2) ∧
        phi_ik ∈ Set.Icc 0 (π / 2) ∧
        phiEF1 f = phi_jk ∧
        gammaVF1 f = arccos (triCos (cos phi_ij) (cos phi_ik) (cos phi_jk))) :
    0 ≤ DeltaPhi T I gammaOutF2 phiEF1 gammaVF1 := by
  apply DeltaPhi_nonneg T I gammaOutF2 phiEF1 gammaVF1
  · -- Show gammaOutF2 terms are nonnegative
    intro f hf
    rcases h_gammaOut_valid f hf with ⟨phi_1, phi_2, phi_3, h1, h2, h3, heq⟩
    rw [heq]
    exact gamma_nonneg h1 h2 h3
  · -- Show F1 terms are nonnegative
    intro f hf
    rcases h_F1_valid f hf with ⟨phi_jk, phi_ij, phi_ik, hjk, hij, hik, heq_phi, heq_gamma⟩
    rw [heq_phi, heq_gamma]
    exact F1_term_nonneg hjk hij hik

end

end ProbabilityCharacter
