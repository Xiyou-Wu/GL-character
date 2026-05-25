import ProbabilityCharacter.Basic
import ProbabilityCharacter.Combinatorics
import ProbabilityCharacter.LowerAverage

/-! # Algebraic corollaries of the average character criterion

This file contains three algebraic corollaries that reduce the verification
of the corrected average character criterion to simpler subset conditions.
-/

namespace ProbabilityCharacter

open scoped BigOperators

noncomputable section

variable {V : Type*}

-- ---------------------------------------------------------------------------
-- Corollary 1: only potentially bad subsets need checking
-- ---------------------------------------------------------------------------

/--
**Corollary 1** (only potentially bad subsets need checking).

Assume `χ(X) < 0`. If for all nonempty connected proper subsets `I ⊂ V` with
`L_Φ(I) ≤ 2π|I|`, we have `ac_Φ(I) > 2π`, then the hyperbolic combinatorial
Ricci flow converges exponentially.

Proof: For any nonempty connected proper subset `I`, either
- `L_Φ(I) > 2π|I|`. Since `Δ_Φ(I) ≥ 0`, we get `ac_Φ(I) > 2π`.
- `L_Φ(I) ≤ 2π|I|`. By the hypothesis, `ac_Φ(I) > 2π`.
-/
theorem corollary_one_only_potentially_bad_subsets
    (vertices : Finset V) (L : V -> ℝ) (Delta B : Finset V -> ℝ) (chi : ℝ)
    (C : Prop)
    [DecidableEq V]
    (IsConnected : Finset V -> Prop)
    (comp : ConnectedComponentFamily vertices B IsConnected)
    (hobstruction :
      ∀ I : Finset V, I.Nonempty -> I ⊆ vertices -> I ≠ vertices ->
        B I = (I.card : ℝ) * (correctedAverage L Delta I - 2 * Real.pi))
    (hchow :
      chi < 0 ->
        (∀ I : Finset V, I.Nonempty -> I ⊆ vertices -> I ≠ vertices -> 0 < B I) ->
        C)
    (hchi : chi < 0)
    (hDelta_nonneg : ∀ I : Finset V, 0 ≤ Delta I)
    (hpotentially_bad :
      ∀ I : Finset V, I.Nonempty -> I ⊆ vertices -> I ≠ vertices ->
        IsConnected I ->
        (∑ i ∈ I, L i) ≤ 2 * Real.pi * (I.card : ℝ) ->
        2 * Real.pi < correctedAverage L Delta I) :
    C := by
  apply hchow hchi
  intro I hI hsub hproper
  let comps := comp.components I hI hsub hproper
  have hcomps_nonempty : comps.Nonempty := by
    have hunion : I = comps.biUnion id := comp.component_union I hI hsub hproper
    rcases hI with ⟨x, hx⟩
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hx_union : x ∈ comps.biUnion id := by
      simpa [hunion] using hx
    simp [h] at hx_union
  have hB_components_pos :
      ∀ J ∈ comps, 0 < B J := by
    intro J hJ
    have hJ_ne : J.Nonempty := comp.component_nonempty I hI hsub hproper J hJ
    have hJ_sub_I : J ⊆ I := comp.component_subset I hI hsub hproper J hJ
    have hJ_sub_vertices : J ⊆ vertices :=
      comp.component_subset_vertices I hI hsub hproper J hJ
    have hJ_connected : IsConnected J := comp.component_connected I hI hsub hproper J hJ
    have hJ_proper : J ≠ vertices := by
      intro hJ_eq
      have hvertices_sub_I : vertices ⊆ I := by
        intro x hx
        exact hJ_sub_I (by simpa [hJ_eq] using hx)
      exact hproper (Finset.Subset.antisymm hsub hvertices_sub_I)
    by_cases hcase : (∑ i ∈ J, L i) ≤ 2 * Real.pi * (J.card : ℝ)
    · have hac_J :=
        hpotentially_bad J hJ_ne hJ_sub_vertices hJ_proper hJ_connected hcase
      exact obstruction_pos_of_correctedAverage_gt L Delta B hJ_ne
        (hobstruction J hJ_ne hJ_sub_vertices hJ_proper) hac_J
    · have hsum : 2 * Real.pi * (J.card : ℝ) < ∑ i ∈ J, L i := by linarith
      have hcard_pos : 0 < (J.card : ℝ) := by
        exact_mod_cast (Finset.card_pos.mpr hJ_ne)
      have htotal : 2 * Real.pi * (J.card : ℝ) < (∑ i ∈ J, L i) + Delta J := by
        linarith [hDelta_nonneg J]
      have hac_J : 2 * Real.pi < correctedAverage L Delta J := by
        rw [correctedAverage]
        apply (mul_lt_mul_iff_of_pos_right hcard_pos).mp
        have hcard_ne : (J.card : ℝ) ≠ 0 := ne_of_gt hcard_pos
        field_simp [hcard_ne]
        linarith
      exact obstruction_pos_of_correctedAverage_gt L Delta B hJ_ne
        (hobstruction J hJ_ne hJ_sub_vertices hJ_proper) hac_J
  rw [comp.B_add I hI hsub hproper]
  exact sum_pos_of_forall_pos comps (fun J => B J) hcomps_nonempty hB_components_pos

-- ---------------------------------------------------------------------------
-- Corollary 2: tangent circle packings (Φ ≡ 0)
-- ---------------------------------------------------------------------------

/--
**Corollary 2** (tangent circle packings).

Assume `Φ ≡ 0` and `χ(X) < 0`. If for every nonempty connected proper subset
`I` with `Σ_{i∈I} d_i ≤ 6|I|`, we have
`Σ_{i∈I}(d_i - 6) + |F_2(I)| + 2|F_1(I)| > 0`,
then the hyperbolic combinatorial Ricci flow converges exponentially to the
unique tangent circle packing.

Proof: This is the special case `φ = 0` of the constant-weight formula.
When `φ = 0`, the constant-weight formula becomes
```
((π/3) · degreeSum + (π/3) · F2 + (2π/3) · F1) / card > 2π
  ↔ degreeSum - 6·card + F2 + 2·F1 > 0
```
and the left-hand side is exactly the corrected average character.
-/
theorem corollary_two_tangent_circle_packings
    (degreeSum F1 F2 card : ℕ) (hcard : 0 < card)
    (htangent :
      (degreeSum : ℝ) - 6 * (card : ℝ) + (F2 : ℝ) + 2 * (F1 : ℝ) > 0) :
    ((Real.pi / 3) * (degreeSum : ℝ) + (Real.pi / 3) * (F2 : ℝ) +
      (2 * Real.pi / 3) * (F1 : ℝ)) / (card : ℝ) > 2 * Real.pi := by
  have hphi0 :=
    constant_weight_formula_nat degreeSum F1 F2 card hcard (0 : ℝ)
  simp only [mul_zero, sub_zero] at hphi0
  have hgoal :
      ((Real.pi / 3) * (degreeSum : ℝ) + (Real.pi / 3) * (F2 : ℝ) +
        (2 * Real.pi / 3) * (F1 : ℝ)) / (card : ℝ) > 2 * Real.pi ↔
      (degreeSum : ℝ) - 6 * (card : ℝ) + (F2 : ℝ) + 2 * (F1 : ℝ) > 0 := by
    simpa using hphi0
  exact hgoal.mpr htangent

-- ---------------------------------------------------------------------------
-- Corollary 3: constant weight, large-set lower average degree criterion
-- ---------------------------------------------------------------------------

/--
**Corollary 3** (constant weight, large-set lower average degree criterion).

Assume `Φ` is constant and `χ(X) < 0`. If there exist `η > 0` and integer
`M ≥ 2` such that for all connected proper subsets `I` with `|I| ≥ M`,
```
(1/|I|) Σ_{i∈I} d_i ≥ 6 + η,
```
and all smaller connected proper subsets satisfy the corrected test, then the
hyperbolic combinatorial Ricci flow converges exponentially.

Proof: For constant weight, `L_i = π d_i / 3`. Therefore for `|I| ≥ M`,
```
(1/|I|) Σ L_i = (π/3) · (1/|I|) Σ d_i ≥ (π/3)(6 + η) = 2π + πη/3 > 2π.
```
This is exactly the lower average character criterion.
-/
theorem corollary_three_large_set_lower_average_degree
    {card : ℕ} (hcard : 0 < card)
    (degreeSum : ℝ) (eta : ℝ) (h_eta_pos : 0 < eta)
    (h_avg_degree :
      degreeSum / (card : ℝ) ≥ 6 + eta) :
    ((Real.pi / 3) * degreeSum) / (card : ℝ) > 2 * Real.pi := by
  have hcard_pos : 0 < (card : ℝ) := by exact_mod_cast hcard
  have h1 : (Real.pi / 3) * degreeSum / (card : ℝ)
      = (Real.pi / 3) * (degreeSum / (card : ℝ)) := by
    field_simp [hcard_pos.ne']
  rw [h1]
  have h2 : (Real.pi / 3) * (degreeSum / (card : ℝ))
      ≥ (Real.pi / 3) * (6 + eta) := by
    apply mul_le_mul_of_nonneg_left
    · exact h_avg_degree
    · positivity
  have h3 : (Real.pi / 3) * (6 + eta) = 2 * Real.pi + (Real.pi / 3) * eta := by
    ring
  have h4 : 2 * Real.pi + (Real.pi / 3) * eta > 2 * Real.pi := by
    have h5 : 0 < (Real.pi / 3) * eta := by
      positivity
    linarith
  linarith [h2, h3, h4]

end

end ProbabilityCharacter
