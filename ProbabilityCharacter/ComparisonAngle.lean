import Mathlib

set_option maxHeartbeats 400000

/-! # Comparison-angle identity

For a face `f = ijk` with edge weights `Φ_ij , Φ_ik , Φ_jk ∈ [0,π/2]`, the
comparison angle at vertex `i` is

```
γ_i^f = arccos[(1+cos Φ_ij+cos Φ_ik−cos Φ_jk)
               /(2√(1+cos Φ_ij)√(1+cos Φ_ik))].
```

The lemma proved here is that these three angles sum to `π`.
The proof interprets the formula as the interior angle of the Euclidean
triangle with side lengths
`ℓ_ij = √(2+2cos Φ_ij)`, etc., and then uses the Euclidean triangle-angle sum.
-/

namespace ProbabilityCharacter

open Real

noncomputable section

variable {V : Type*}

/-- The cosine term of one Euclidean unit packing angle. -/
def triCos (a b c : Real) : Real :=
  (1 + a + b - c) / (2 * Real.sqrt (1 + a) * Real.sqrt (1 + b))

/-- A triangular face together with the three edge weights (cosines). -/
structure WeightedTriFace (V : Type*) [DecidableEq V] where
  verts : Finset V
  card_verts : verts.card = 3
  v1 : V
  v2 : V
  v3 : V
  v1_ne_v2 : v1 ≠ v2
  v1_ne_v3 : v1 ≠ v3
  v2_ne_v3 : v2 ≠ v3
  verts_eq : verts = {v1, v2, v3}
  cosPhi12 : ℝ
  cosPhi13 : ℝ
  cosPhi23 : ℝ

namespace WeightedTriFace

variable {V : Type*} [DecidableEq V]
variable (f : WeightedTriFace V)

def ell12 : ℝ := Real.sqrt (2 + 2 * f.cosPhi12)
def ell13 : ℝ := Real.sqrt (2 + 2 * f.cosPhi13)
def ell23 : ℝ := Real.sqrt (2 + 2 * f.cosPhi23)

def gamma1 : ℝ := Real.arccos (triCos f.cosPhi12 f.cosPhi13 f.cosPhi23)
def gamma2 : ℝ := Real.arccos (triCos f.cosPhi12 f.cosPhi23 f.cosPhi13)
def gamma3 : ℝ := Real.arccos (triCos f.cosPhi13 f.cosPhi23 f.cosPhi12)

end WeightedTriFace

open WeightedTriFace

/-- Hypotheses ensuring the three edge lengths form a genuine Euclidean triangle. -/
structure EuclideanTriangleHyp {V : Type*} [DecidableEq V] (f : WeightedTriFace V) : Prop where
  pos1  : 0 < f.ell12
  pos2  : 0 < f.ell13
  pos3  : 0 < f.ell23
  tri12 : f.ell23 < f.ell12 + f.ell13
  tri13 : f.ell13 < f.ell12 + f.ell23
  tri23 : f.ell12 < f.ell13 + f.ell23

/-- For a Euclidean triangle with side lengths a,b,c, the cosine of the angle
opposite side c is `(a²+b²−c²)/(2ab)`. -/
def euclideanCosAngle (a b c : ℝ) : ℝ :=
  (a^2 + b^2 - c^2) / (2 * a * b)

/-- The `triCos` expression equals the Euclidean cosine-law expression. -/
lemma triCos_eq_euclideanCosAngle
    (a b c : ℝ) (ha : -1 < a) (hb : -1 < b) (hc : -1 < c) :
    triCos a b c =
      euclideanCosAngle (Real.sqrt (2 + 2 * a)) (Real.sqrt (2 + 2 * b))
                        (Real.sqrt (2 + 2 * c)) := by
  have ha2 : 0 < 2 + 2 * a := by linarith
  have hb2 : 0 < 2 + 2 * b := by linarith
  have hc2 : 0 ≤ 2 + 2 * c := by linarith
  have hsa : Real.sqrt (2 + 2 * a) ^ 2 = 2 + 2 * a := Real.sq_sqrt (by linarith)
  have hsb : Real.sqrt (2 + 2 * b) ^ 2 = 2 + 2 * b := Real.sq_sqrt (by linarith)
  have hsc : Real.sqrt (2 + 2 * c) ^ 2 = 2 + 2 * c := Real.sq_sqrt hc2
  have h1 : Real.sqrt (2 + 2 * a) ≠ 0 := by
    apply Real.sqrt_ne_zero'.mpr
    linarith
  have h2 : Real.sqrt (2 + 2 * b) ≠ 0 := by
    apply Real.sqrt_ne_zero'.mpr
    linarith
  have hsqrt2 : Real.sqrt (2 + 2 * a) = Real.sqrt 2 * Real.sqrt (1 + a) := by
    rw [show 2 + 2 * a = (2 : ℝ) * (1 + a) by ring]
    exact Real.sqrt_mul (by norm_num) (1 + a)
  have hsqrt2b : Real.sqrt (2 + 2 * b) = Real.sqrt 2 * Real.sqrt (1 + b) := by
    rw [show 2 + 2 * b = (2 : ℝ) * (1 + b) by ring]
    exact Real.sqrt_mul (by norm_num) (1 + b)
  have h3 : Real.sqrt (1 + a) ≠ 0 := by
    apply Real.sqrt_ne_zero'.mpr
    linarith
  have h4 : Real.sqrt (1 + b) ≠ 0 := by
    apply Real.sqrt_ne_zero'.mpr
    linarith
  have h5 : 2 * Real.sqrt (1 + a) * Real.sqrt (1 + b) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero; norm_num; exact h3
    · exact h4
  have hsc_ne : Real.sqrt (2 + 2 * c) ≠ 0 := by
    apply Real.sqrt_ne_zero'.mpr
    linarith
  have h1a : Real.sqrt (1 + a) ^ 2 = 1 + a := Real.sq_sqrt (by linarith)
  have h1b : Real.sqrt (1 + b) ^ 2 = 1 + b := Real.sq_sqrt (by linarith)
  simp only [triCos, euclideanCosAngle, hsqrt2, hsqrt2b]
  have h6 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have h2c : Real.sqrt (2 + 2 * c) ^ 2 = 2 + 2 * c := hsc
  have h2c' : Real.sqrt (2 + c * 2) ^ 2 = 2 + c * 2 := by
    have : (2 + c * 2 : ℝ) = (2 + 2 * c : ℝ) := by ring
    rw [this]
    exact hsc
  field_simp [h5, h6, hsc_ne]
  <;> ring_nf
  <;> simp only [h1a, h1b, h2c', h6]
  <;> ring

/-- For angles A,B ∈ (0,π), we have A+B < π ↔ cosA + cosB > 0. -/
lemma angle_sum_lt_pi_iff_cos_sum_pos {A B : ℝ} (hA : A ∈ Set.Ioo 0 Real.pi) (hB : B ∈ Set.Ioo 0 Real.pi) :
    A + B < Real.pi ↔ Real.cos A + Real.cos B > 0 := by
  have hA1 : 0 < A := hA.1
  have hA2 : A < Real.pi := hA.2
  have hB1 : 0 < B := hB.1
  have hB2 : B < Real.pi := hB.2
  constructor
  · intro h
    have h1 : B < Real.pi - A := by linarith
    have h2 : 0 < Real.pi - A := by nlinarith [hA1, hA2, Real.pi_pos]
    have h3 : Real.pi - A < Real.pi := by nlinarith [hA1, Real.pi_pos]
    have h4 : Real.cos B > Real.cos (Real.pi - A) := by
      refine Real.cos_lt_cos_of_nonneg_of_le_pi ?_ ?_ h1
      · linarith [hB1]
      · linarith [hA1, Real.pi_pos]
    have h5 : Real.cos (Real.pi - A) = -Real.cos A := by rw [Real.cos_pi_sub]
    rw [h5] at h4
    linarith
  · intro h
    have h1 : Real.cos B > -Real.cos A := by linarith
    have h2 : Real.cos (Real.pi - A) = -Real.cos A := by rw [Real.cos_pi_sub]
    rw [← h2] at h1
    have h3 : 0 ≤ B := by linarith
    have h4 : B ≤ Real.pi := by linarith
    have h5 : 0 ≤ Real.pi - A := by nlinarith [hA1, hA2, Real.pi_pos]
    have h6 : Real.pi - A ≤ Real.pi := by nlinarith [hA1, Real.pi_pos]
    have h7 : B < Real.pi - A := by
      by_contra h8
      push_neg at h8
      have h9 : Real.cos B ≤ Real.cos (Real.pi - A) := by
        refine Real.cos_le_cos_of_nonneg_of_le_pi ?_ ?_ h8
        · linarith [hB1]
        · linarith [hA1, Real.pi_pos]
      linarith [h1, h9]
    linarith

set_option maxHeartbeats 800000 in
/-- The three comparison angles of a weighted triangular face sum to `π`. -/
theorem comparison_angle_sum_eq_pi
    {V : Type*} [DecidableEq V]
    (f : WeightedTriFace V)
    (hEuc : EuclideanTriangleHyp f)
    (hcos1 : -1 < f.cosPhi12) (hcos2 : -1 < f.cosPhi13) (hcos3 : -1 < f.cosPhi23)
    (hangle1 : 0 < gamma1 f ∧ gamma1 f < Real.pi)
    (hangle2 : 0 < gamma2 f ∧ gamma2 f < Real.pi)
    (hangle3 : 0 < gamma3 f ∧ gamma3 f < Real.pi) :
    gamma1 f + gamma2 f + gamma3 f = Real.pi := by
  -- Rewrite each gamma as the arccos of the Euclidean cosine-law expression.
  have h1 : gamma1 f = Real.arccos (euclideanCosAngle (ell12 f) (ell13 f) (ell23 f)) := by
    rw [gamma1, triCos_eq_euclideanCosAngle f.cosPhi12 f.cosPhi13 f.cosPhi23 hcos1 hcos2 hcos3]
    simp [ell12, ell13, ell23]
  have h2 : gamma2 f = Real.arccos (euclideanCosAngle (ell12 f) (ell23 f) (ell13 f)) := by
    rw [gamma2, triCos_eq_euclideanCosAngle f.cosPhi12 f.cosPhi23 f.cosPhi13 hcos1 hcos3 hcos2]
    simp [ell12, ell13, ell23]
  have h3 : gamma3 f = Real.arccos (euclideanCosAngle (ell13 f) (ell23 f) (ell12 f)) := by
    rw [gamma3, triCos_eq_euclideanCosAngle f.cosPhi13 f.cosPhi23 f.cosPhi12 hcos2 hcos3 hcos1]
    simp [ell12, ell13, ell23]
  -- Now we prove that the three arccos angles sum to π.
  -- This is the classical Euclidean triangle angle sum.
  set A := Real.arccos (euclideanCosAngle (ell12 f) (ell13 f) (ell23 f)) with hA
  set B := Real.arccos (euclideanCosAngle (ell12 f) (ell23 f) (ell13 f)) with hB
  set C := Real.arccos (euclideanCosAngle (ell13 f) (ell23 f) (ell12 f)) with hC
  clear_value A B C
  -- Step 1: Show A, B, C are in (0, π)
  have hA1 : 0 < A := by rw [← h1]; exact hangle1.1
  have hA2 : A < Real.pi := by rw [← h1]; exact hangle1.2
  have hB1 : 0 < B := by rw [← h2]; exact hangle2.1
  have hB2 : B < Real.pi := by rw [← h2]; exact hangle2.2
  have hC1 : 0 < C := by rw [← h3]; exact hangle3.1
  have hC2 : C < Real.pi := by rw [← h3]; exact hangle3.2
  -- Step 2: Compute cos A, cos B, cos C from the cosine law
  have hcosA : Real.cos A = euclideanCosAngle (ell12 f) (ell13 f) (ell23 f) := by
    rw [hA]
    apply Real.cos_arccos
    · -- Show the expression is ≥ -1
      have h1 : ell12 f > 0 := hEuc.pos1
      have h2 : ell13 f > 0 := hEuc.pos2
      have h3 : ell23 f > 0 := hEuc.pos3
      have htri1 : ell23 f < ell12 f + ell13 f := hEuc.tri12
      have htri2 : ell13 f < ell12 f + ell23 f := hEuc.tri13
      have htri3 : ell12 f < ell13 f + ell23 f := hEuc.tri23
      have h : euclideanCosAngle (ell12 f) (ell13 f) (ell23 f) ≥ -1 := by
        unfold euclideanCosAngle
        have hnum : (ell12 f)^2 + (ell13 f)^2 - (ell23 f)^2 ≥ -2 * (ell12 f) * (ell13 f) := by
          nlinarith [sq_nonneg (ell12 f - ell13 f + ell23 f), sq_nonneg (ell12 f + ell13 f - ell23 f),
            sq_pos_of_pos h1, sq_pos_of_pos h2, sq_pos_of_pos h3]
        have hden : 0 < 2 * (ell12 f) * (ell13 f) := by positivity
        apply (le_div_iff₀ hden).mpr
        linarith
      linarith
    · -- Show the expression is ≤ 1
      have h1 : ell12 f > 0 := hEuc.pos1
      have h2 : ell13 f > 0 := hEuc.pos2
      have h3 : ell23 f > 0 := hEuc.pos3
      have htri1 : ell23 f < ell12 f + ell13 f := hEuc.tri12
      have htri2 : ell13 f < ell12 f + ell23 f := hEuc.tri13
      have htri3 : ell12 f < ell13 f + ell23 f := hEuc.tri23
      have h : euclideanCosAngle (ell12 f) (ell13 f) (ell23 f) ≤ 1 := by
        unfold euclideanCosAngle
        have hnum : (ell12 f)^2 + (ell13 f)^2 - (ell23 f)^2 ≤ 2 * (ell12 f) * (ell13 f) := by
          nlinarith [sq_nonneg (ell12 f - ell13 f + ell23 f), sq_nonneg (ell12 f - ell13 f - ell23 f),
            sq_nonneg (ell12 f + ell13 f - ell23 f), sq_nonneg (ell12 f - ell13 f + ell23 f), sq_nonneg (ell12 f + ell13 f + ell23 f),
            sq_pos_of_pos h1, sq_pos_of_pos h2, sq_pos_of_pos h3, htri1, htri2, htri3]
        have hden : 0 < 2 * (ell12 f) * (ell13 f) := by positivity
        apply (div_le_iff₀ hden).mpr
        linarith
      linarith
  have hcosB : Real.cos B = euclideanCosAngle (ell12 f) (ell23 f) (ell13 f) := by
    rw [hB]
    apply Real.cos_arccos
    · -- Show ≥ -1
      have h1 : ell12 f > 0 := hEuc.pos1
      have h2 : ell13 f > 0 := hEuc.pos2
      have h3 : ell23 f > 0 := hEuc.pos3
      have htri1 : ell23 f < ell12 f + ell13 f := hEuc.tri12
      have htri2 : ell13 f < ell12 f + ell23 f := hEuc.tri13
      have htri3 : ell12 f < ell13 f + ell23 f := hEuc.tri23
      have h : euclideanCosAngle (ell12 f) (ell23 f) (ell13 f) ≥ -1 := by
        unfold euclideanCosAngle
        have hnum : (ell12 f)^2 + (ell23 f)^2 - (ell13 f)^2 ≥ -2 * (ell12 f) * (ell23 f) := by
          nlinarith [sq_nonneg (ell12 f - ell23 f + ell13 f), sq_nonneg (ell12 f + ell23 f - ell13 f),
            sq_pos_of_pos h1, sq_pos_of_pos h2, sq_pos_of_pos h3]
        have hden : 0 < 2 * (ell12 f) * (ell23 f) := by positivity
        apply (le_div_iff₀ hden).mpr
        linarith
      linarith
    · -- Show ≤ 1
      have h1 : ell12 f > 0 := hEuc.pos1
      have h2 : ell13 f > 0 := hEuc.pos2
      have h3 : ell23 f > 0 := hEuc.pos3
      have htri1 : ell23 f < ell12 f + ell13 f := hEuc.tri12
      have htri2 : ell13 f < ell12 f + ell23 f := hEuc.tri13
      have htri3 : ell12 f < ell13 f + ell23 f := hEuc.tri23
      have h : euclideanCosAngle (ell12 f) (ell23 f) (ell13 f) ≤ 1 := by
        unfold euclideanCosAngle
        have hnum : (ell12 f)^2 + (ell23 f)^2 - (ell13 f)^2 ≤ 2 * (ell12 f) * (ell23 f) := by
          nlinarith [sq_nonneg (ell12 f - ell23 f + ell13 f), sq_nonneg (ell12 f - ell23 f - ell13 f),
            sq_nonneg (ell12 f + ell23 f - ell13 f), sq_nonneg (ell12 f - ell23 f + ell13 f), sq_nonneg (ell12 f + ell23 f + ell13 f),
            sq_pos_of_pos h1, sq_pos_of_pos h2, sq_pos_of_pos h3, htri1, htri2, htri3]
        have hden : 0 < 2 * (ell12 f) * (ell23 f) := by positivity
        apply (div_le_iff₀ hden).mpr
        linarith
      linarith
  have hcosC : Real.cos C = euclideanCosAngle (ell13 f) (ell23 f) (ell12 f) := by
    rw [hC]
    apply Real.cos_arccos
    · -- Show ≥ -1
      have h1 : ell12 f > 0 := hEuc.pos1
      have h2 : ell13 f > 0 := hEuc.pos2
      have h3 : ell23 f > 0 := hEuc.pos3
      have htri1 : ell23 f < ell12 f + ell13 f := hEuc.tri12
      have htri2 : ell13 f < ell12 f + ell23 f := hEuc.tri13
      have htri3 : ell12 f < ell13 f + ell23 f := hEuc.tri23
      have h : euclideanCosAngle (ell13 f) (ell23 f) (ell12 f) ≥ -1 := by
        unfold euclideanCosAngle
        have hnum : (ell13 f)^2 + (ell23 f)^2 - (ell12 f)^2 ≥ -2 * (ell13 f) * (ell23 f) := by
          nlinarith [sq_nonneg (ell13 f - ell23 f + ell12 f), sq_nonneg (ell13 f + ell23 f - ell12 f),
            sq_pos_of_pos h1, sq_pos_of_pos h2, sq_pos_of_pos h3]
        have hden : 0 < 2 * (ell13 f) * (ell23 f) := by positivity
        apply (le_div_iff₀ hden).mpr
        linarith
      linarith
    · -- Show ≤ 1
      have h1 : ell12 f > 0 := hEuc.pos1
      have h2 : ell13 f > 0 := hEuc.pos2
      have h3 : ell23 f > 0 := hEuc.pos3
      have htri1 : ell23 f < ell12 f + ell13 f := hEuc.tri12
      have htri2 : ell13 f < ell12 f + ell23 f := hEuc.tri13
      have htri3 : ell12 f < ell13 f + ell23 f := hEuc.tri23
      have h : euclideanCosAngle (ell13 f) (ell23 f) (ell12 f) ≤ 1 := by
        unfold euclideanCosAngle
        have hnum : (ell13 f)^2 + (ell23 f)^2 - (ell12 f)^2 ≤ 2 * (ell13 f) * (ell23 f) := by
          nlinarith [sq_nonneg (ell13 f - ell23 f + ell12 f), sq_nonneg (ell13 f - ell23 f - ell12 f),
            sq_nonneg (ell13 f + ell23 f - ell12 f), sq_nonneg (ell12 f + ell13 f - ell23 f), sq_nonneg (ell12 f - ell13 f + ell23 f),
            sq_pos_of_pos h1, sq_pos_of_pos h2, sq_pos_of_pos h3, htri1, htri2, htri3]
        have hden : 0 < 2 * (ell13 f) * (ell23 f) := by positivity
        apply (div_le_iff₀ hden).mpr
        linarith
      linarith
  -- Step 3: Show A + B < π using the lemma angle_sum_lt_pi_iff_cos_sum_pos
  have hAB_lt_pi : A + B < Real.pi := by
    have hA_Ioo : A ∈ Set.Ioo 0 Real.pi := ⟨hA1, hA2⟩
    have hB_Ioo : B ∈ Set.Ioo 0 Real.pi := ⟨hB1, hB2⟩
    rw [angle_sum_lt_pi_iff_cos_sum_pos hA_Ioo hB_Ioo]
    -- Show cos A + cos B > 0
    rw [hcosA, hcosB]
    unfold euclideanCosAngle
    have h1 : ell12 f > 0 := hEuc.pos1
    have h2 : ell13 f > 0 := hEuc.pos2
    have h3 : ell23 f > 0 := hEuc.pos3
    have htri3 : ell12 f < ell13 f + ell23 f := hEuc.tri23
    have hsum_pos : ((ell12 f)^2 + (ell13 f)^2 - (ell23 f)^2) / (2 * (ell12 f) * (ell13 f)) + ((ell12 f)^2 + (ell23 f)^2 - (ell13 f)^2) / (2 * (ell12 f) * (ell23 f)) > 0 := by
      have htri1 : ell23 f < ell12 f + ell13 f := hEuc.tri12
      have htri2 : ell13 f < ell12 f + ell23 f := hEuc.tri13
      -- Key algebraic identity: the numerator factors as (b+c)(a-b+c)(a+b-c)
      have hfactor : ((ell12 f)^2 + (ell13 f)^2 - (ell23 f)^2) * (ell23 f) + ((ell12 f)^2 + (ell23 f)^2 - (ell13 f)^2) * (ell13 f)
          = (ell13 f + ell23 f) * (ell12 f - ell13 f + ell23 f) * (ell12 f + ell13 f - ell23 f) := by ring
      have hnum : ((ell12 f)^2 + (ell13 f)^2 - (ell23 f)^2) * (ell23 f) + ((ell12 f)^2 + (ell23 f)^2 - (ell13 f)^2) * (ell13 f) > 0 := by
        rw [hfactor]
        have h1' : ell13 f + ell23 f > 0 := by positivity
        have h2' : ell12 f - ell13 f + ell23 f > 0 := by linarith [htri2]
        have h3' : ell12 f + ell13 f - ell23 f > 0 := by linarith [htri1]
        positivity
      have hden : 0 < 2 * (ell12 f) * (ell13 f) * (ell23 f) := by positivity
      have hleft : ((ell12 f)^2 + (ell13 f)^2 - (ell23 f)^2) / (2 * (ell12 f) * (ell13 f))
          = ((ell12 f)^2 + (ell13 f)^2 - (ell23 f)^2) * (ell23 f) / (2 * (ell12 f) * (ell13 f) * (ell23 f)) := by
        field_simp
        <;> ring
      have hright : ((ell12 f)^2 + (ell23 f)^2 - (ell13 f)^2) / (2 * (ell12 f) * (ell23 f))
          = ((ell12 f)^2 + (ell23 f)^2 - (ell13 f)^2) * (ell13 f) / (2 * (ell12 f) * (ell13 f) * (ell23 f)) := by
        field_simp
        <;> ring
      rw [hleft, hright]
      have hnum' : ((ell12 f)^2 + (ell13 f)^2 - (ell23 f)^2) * (ell23 f) + ((ell12 f)^2 + (ell23 f)^2 - (ell13 f)^2) * (ell13 f) > 0 := hnum
      have hcombined :
        ((ell12 f)^2 + (ell13 f)^2 - (ell23 f)^2) * (ell23 f) / (2 * (ell12 f) * (ell13 f) * (ell23 f)) + ((ell12 f)^2 + (ell23 f)^2 - (ell13 f)^2) * (ell13 f) / (2 * (ell12 f) * (ell13 f) * (ell23 f))
        = (((ell12 f)^2 + (ell13 f)^2 - (ell23 f)^2) * (ell23 f) + ((ell12 f)^2 + (ell23 f)^2 - (ell13 f)^2) * (ell13 f)) / (2 * (ell12 f) * (ell13 f) * (ell23 f)) := by
        ring
      rw [hcombined]
      apply div_pos
      · exact hnum'
      · exact hden
    linarith
  -- Step 4: Show cos(A + B) = -cos(C)
  -- We use the cosine addition formula: cos(A+B) = cosA cosB - sinA sinB
  -- For a Euclidean triangle, this identity holds: cos(A+B) = -cos(C)
  -- The proof uses the fact that sin A = 2*Area/(bc), etc.
  have hcosAB_eq_neg_cosC : Real.cos (A + B) = -Real.cos C := by
    rw [Real.cos_add]
    rw [hcosA, hcosB, hcosC]
    -- Standard identity for Euclidean triangles: cos(A+B) = -cos(C).
    -- Equivalently, cos A cos B - sin A sin B = -cos C.
    have hsinA_pos : 0 < Real.sin A := by apply Real.sin_pos_of_pos_of_lt_pi; linarith; linarith
    have hsinB_pos : 0 < Real.sin B := by apply Real.sin_pos_of_pos_of_lt_pi; linarith; linarith
    have hsinA_sq : Real.sin A ^ 2 = 1 - Real.cos A ^ 2 := by
      have h : Real.sin A ^ 2 + Real.cos A ^ 2 = 1 := Real.sin_sq_add_cos_sq A
      linarith
    have hsinB_sq : Real.sin B ^ 2 = 1 - Real.cos B ^ 2 := by
      have h : Real.sin B ^ 2 + Real.cos B ^ 2 = 1 := Real.sin_sq_add_cos_sq B
      linarith
    have hsinA : Real.sin A = Real.sqrt (1 - Real.cos A ^ 2) := by
      have h : Real.sqrt (Real.sin A ^ 2) = Real.sin A := Real.sqrt_sq (le_of_lt hsinA_pos)
      rw [hsinA_sq] at h
      exact h.symm
    have hsinB : Real.sin B = Real.sqrt (1 - Real.cos B ^ 2) := by
      have h : Real.sqrt (Real.sin B ^ 2) = Real.sin B := Real.sqrt_sq (le_of_lt hsinB_pos)
      rw [hsinB_sq] at h
      exact h.symm
    rw [hsinA, hsinB]
    -- Now we need to prove: cosA cosB - sqrt((1-cos^2 A)(1-cos^2 B)) = -cosC
    -- Equivalently: cosA cosB + cosC = sqrt((1-cos^2 A)(1-cos^2 B))
    have h1 : Real.cos A * Real.cos B + Real.cos C >= 0 := by
      rw [hcosA, hcosB, hcosC]
      unfold euclideanCosAngle
      have ha : 0 < ell12 f := hEuc.pos1
      have hb : 0 < ell13 f := hEuc.pos2
      have hc : 0 < ell23 f := hEuc.pos3
      have htri1 : ell23 f < ell12 f + ell13 f := hEuc.tri12
      have htri2 : ell13 f < ell12 f + ell23 f := hEuc.tri13
      have htri3 : ell12 f < ell13 f + ell23 f := hEuc.tri23
      -- The key identity: cosA*cosB + cosC = (N1*N2 + 2*a^2*N3) / (4*a^2*b*c)
      -- where N1 = a^2+b^2-c^2, N2 = a^2+c^2-b^2, N3 = b^2+c^2-a^2
      -- And N1*N2 + 2*a^2*N3 = (b+c-a)(b+c+a)(a+c-b)(a+b-c) > 0 for a non-degenerate triangle
      have hnum_pos : ((ell12 f) ^ 2 + (ell13 f) ^ 2 - (ell23 f) ^ 2) * ((ell12 f) ^ 2 + (ell23 f) ^ 2 - (ell13 f) ^ 2) + 2 * (ell12 f) ^ 2 * ((ell13 f) ^ 2 + (ell23 f) ^ 2 - (ell12 f) ^ 2) > 0 := by
        have hfactor : ((ell12 f) ^ 2 + (ell13 f) ^ 2 - (ell23 f) ^ 2) * ((ell12 f) ^ 2 + (ell23 f) ^ 2 - (ell13 f) ^ 2) + 2 * (ell12 f) ^ 2 * ((ell13 f) ^ 2 + (ell23 f) ^ 2 - (ell12 f) ^ 2)
            = (ell13 f + ell23 f - ell12 f) * (ell13 f + ell23 f + ell12 f) * (ell12 f + ell23 f - ell13 f) * (ell12 f + ell13 f - ell23 f) := by ring
        rw [hfactor]
        have h1 : ell13 f + ell23 f - ell12 f > 0 := by linarith [hEuc.tri23]
        have h2 : ell13 f + ell23 f + ell12 f > 0 := by positivity
        have h3 : ell12 f + ell23 f - ell13 f > 0 := by linarith [hEuc.tri13]
        have h4 : ell12 f + ell13 f - ell23 f > 0 := by linarith [hEuc.tri12]
        positivity
      have hleft : (((ell12 f) ^ 2 + (ell13 f) ^ 2 - (ell23 f) ^ 2) / (2 * (ell12 f) * (ell13 f))) * (((ell12 f) ^ 2 + (ell23 f) ^ 2 - (ell13 f) ^ 2) / (2 * (ell12 f) * (ell23 f))) + ((ell13 f) ^ 2 + (ell23 f) ^ 2 - (ell12 f) ^ 2) / (2 * (ell13 f) * (ell23 f))
          = (((ell12 f) ^ 2 + (ell13 f) ^ 2 - (ell23 f) ^ 2) * ((ell12 f) ^ 2 + (ell23 f) ^ 2 - (ell13 f) ^ 2) + 2 * (ell12 f) ^ 2 * ((ell13 f) ^ 2 + (ell23 f) ^ 2 - (ell12 f) ^ 2)) / (4 * (ell12 f) ^ 2 * (ell13 f) * (ell23 f)) := by
        field_simp
        ring
      rw [hleft]
      apply div_nonneg
      · nlinarith
      · positivity
    have h2 : (Real.cos A * Real.cos B + Real.cos C) ^ 2 = (1 - Real.cos A ^ 2) * (1 - Real.cos B ^ 2) := by
      rw [hcosA, hcosB, hcosC]
      unfold euclideanCosAngle
      have ha : 0 < ell12 f := hEuc.pos1
      have hb : 0 < ell13 f := hEuc.pos2
      have hc : 0 < ell23 f := hEuc.pos3
      have hden1 : 2 * (ell12 f) * (ell13 f) ≠ 0 := by positivity
      have hden2 : 2 * (ell12 f) * (ell23 f) ≠ 0 := by positivity
      have hden3 : 2 * (ell13 f) * (ell23 f) ≠ 0 := by positivity
      field_simp
      ring
    have h3 : Real.cos A * Real.cos B + Real.cos C = Real.sqrt ((1 - Real.cos A ^ 2) * (1 - Real.cos B ^ 2)) := by
      have h3a : Real.sqrt ((1 - Real.cos A ^ 2) * (1 - Real.cos B ^ 2)) ^ 2 = (1 - Real.cos A ^ 2) * (1 - Real.cos B ^ 2) := by
        rw [Real.sq_sqrt]
        nlinarith [Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B, hsinA_sq, hsinB_sq]
      have h3b : Real.cos A * Real.cos B + Real.cos C >= 0 := h1
      have h3c : Real.sqrt ((1 - Real.cos A ^ 2) * (1 - Real.cos B ^ 2)) >= 0 := Real.sqrt_nonneg _
      nlinarith [h2, h3a, h3b, h3c, Real.sqrt_nonneg ((1 - Real.cos A ^ 2) * (1 - Real.cos B ^ 2))]
    have h4 : Real.cos A * Real.cos B - Real.sqrt ((1 - Real.cos A ^ 2) * (1 - Real.cos B ^ 2)) = -Real.cos C := by
      linarith [h3]
    have hsqrt_mul : Real.sqrt (1 - Real.cos A ^ 2) * Real.sqrt (1 - Real.cos B ^ 2) = Real.sqrt ((1 - Real.cos A ^ 2) * (1 - Real.cos B ^ 2)) := by
      rw [← Real.sqrt_mul (by nlinarith [Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B])]
    rw [hsqrt_mul]
    rw [← hcosA, ← hcosB, ← hcosC]
    exact h4
  -- Step 5: Since A + B < π and cos(A + B) = cos(π - C), and both are in [0, π], we get A + B = π - C
  have hpi_minus_C : Real.cos (A + B) = Real.cos (Real.pi - C) := by
    rw [hcosAB_eq_neg_cosC]
    rw [Real.cos_pi_sub]
  have hA_plus_B_in_range : A + B ∈ Set.Icc 0 Real.pi := by
    constructor
    · nlinarith
    · linarith [hAB_lt_pi]
  have hpi_minus_C_in_range : Real.pi - C ∈ Set.Icc 0 Real.pi := by
    constructor
    · nlinarith [hC1, hC2, Real.pi_pos]
    · nlinarith [hC1, hC2, Real.pi_pos]
  have hA_plus_B_eq_pi_minus_C : A + B = Real.pi - C := by
    apply Real.injOn_cos hA_plus_B_in_range hpi_minus_C_in_range hpi_minus_C
  linarith [hA_plus_B_eq_pi_minus_C]

end

end ProbabilityCharacter
