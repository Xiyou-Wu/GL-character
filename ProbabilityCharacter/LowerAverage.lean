import Mathlib
import ProbabilityCharacter.Basic

/-! # Lower average character criterion

This file formalises the corollary that a lower-average hypothesis on
*connected* proper subsets, together with a corrected-average hypothesis on
small connected subsets, implies the full average-character criterion.

The proof proceeds by decomposing an arbitrary nonempty proper subset `I`
into its connected components `I₁,…,Iₛ` (in the one-skeleton of the full
subcomplex).  The obstruction `B_Φ` is additive over this decomposition,
because every triangle contributing to `B_Φ(I)` has its vertices in a single
component.  Each component is treated according to its cardinality:

* large components (`|Iₐ| ≥ M`) satisfy the uncorrected lower-average
  hypothesis, and together with the non-negativity of the boundary correction
  `Δ_Φ` this yields `B_Φ(Iₐ) > 0`;

* small components (`|Iₐ| < M`) satisfy the corrected-average hypothesis
  directly, which again gives `B_Φ(Iₐ) > 0` by the obstruction identity.

Hence `B_Φ(I) > 0` for every nonempty proper `I`.  Combined with the
assumption `χ(X) < 0` (which already gives `ac_Φ(V) > 2π` via the Ge--Lin
average character formula), the abstract `average_character_criterion_skeleton`
applies.

Because the full combinatorial construction of connected components of the
subcomplex is not yet formalised, the decomposition is introduced as an
explicit hypothesis family.  This gives a *skeleton* version of the criterion
that is fully mathematically rigorous once the component family is supplied.
-/

namespace ProbabilityCharacter

open scoped BigOperators

noncomputable section

variable {V : Type*} [DecidableEq V]

/--
A family of connected-component decompositions for subsets of vertices.

For every nonempty proper subset `I ⊆ vertices`, `connectedComponents I` is a finite
family of nonempty subsets `J` such that

* the `J` are pairwise disjoint and their union is `I`;
* each `J` is connected in the one-skeleton of the triangulation (recorded by
  the abstract predicate `IsConnected`);
* the obstruction `B` is additive over the family.

In a future refinement this structure can be constructed from the
1-skeleton of the full subcomplex `F_I`.
-/
structure ConnectedComponentFamily
    (vertices : Finset V) (B : Finset V → ℝ) (IsConnected : Finset V → Prop) where
  /-- The components of a nonempty proper subset. -/
  components :
    (I : Finset V) → I.Nonempty → I ⊆ vertices → I ≠ vertices → Finset (Finset V)
  /-- Every component is nonempty. -/
  component_nonempty :
    ∀ (I : Finset V) (hI : I.Nonempty) (hsub : I ⊆ vertices)
      (hproper : I ≠ vertices) (J : Finset V),
      J ∈ components I hI hsub hproper → J.Nonempty
  /-- Every component is contained in the original subset. -/
  component_subset :
    ∀ (I : Finset V) (hI : I.Nonempty) (hsub : I ⊆ vertices)
      (hproper : I ≠ vertices) (J : Finset V),
      J ∈ components I hI hsub hproper → J ⊆ I
  /-- Every component is connected. -/
  component_connected :
    ∀ (I : Finset V) (hI : I.Nonempty) (hsub : I ⊆ vertices)
      (hproper : I ≠ vertices) (J : Finset V),
      J ∈ components I hI hsub hproper → IsConnected J
  /-- Components are pairwise disjoint. -/
  component_disjoint :
    ∀ (I : Finset V) (hI : I.Nonempty) (hsub : I ⊆ vertices)
      (hproper : I ≠ vertices) (J₁ J₂ : Finset V),
      J₁ ∈ components I hI hsub hproper → J₂ ∈ components I hI hsub hproper →
      J₁ ≠ J₂ →
      Disjoint J₁ J₂
  /-- The union of the components equals the original set. -/
  component_union :
    ∀ (I : Finset V) (hI : I.Nonempty) (hsub : I ⊆ vertices)
      (hproper : I ≠ vertices),
      I = (components I hI hsub hproper).biUnion id
  /-- Every component is a subset of the full vertex set. -/
  component_subset_vertices :
    ∀ (I : Finset V) (hI : I.Nonempty) (hsub : I ⊆ vertices)
      (hproper : I ≠ vertices) (J : Finset V),
      J ∈ components I hI hsub hproper → J ⊆ vertices
  /-- The obstruction `B` is additive over the decomposition. -/
  B_add :
    ∀ (I : Finset V) (hI : I.Nonempty) (hsub : I ⊆ vertices)
      (hproper : I ≠ vertices),
      B I = ∑ J ∈ components I hI hsub hproper, B J

section AdditivityLemmas

/--
If a finite sum of real numbers is taken over a finset of nonempty sets,
and every summand is strictly positive, then the total sum is strictly
positive.
-/
theorem sum_pos_of_forall_pos {α : Type*} (s : Finset α) (f : α → ℝ)
    (hne : s.Nonempty) (hf : ∀ a ∈ s, 0 < f a) : 0 < ∑ a ∈ s, f a := by
  exact Finset.sum_pos hf hne

end AdditivityLemmas

section LowerAverageCriterion

/--
The lower average character criterion (skeleton version).

**Assumptions**

* `vertices` – the full vertex set, nonempty;
* `L` – the character function `L_Φ` on vertices;
* `Delta` – the boundary correction `Δ_Φ` on vertex subsets;
* `B` – the Chow–Luo obstruction `B_Φ` on vertex subsets;
* `chi` – the Euler characteristic `χ(X)`;
* `C` – the external conclusion (existence, uniqueness, and flow convergence);
* `η > 0` and `M ≥ 1` – the threshold constants;
* `IsConnected` – the connectedness predicate for vertex subsets;
* `comp` – a connected-component family for `B`;
* `hobstruction` – the obstruction identity on every nonempty proper subset;
* `hchow` – Chow–Luo's theorem: negative Euler characteristic and positive
  obstructions imply `C`;
* `hchi` – the Euler characteristic is negative;
* `hlarge` – for every connected proper subset of size at least `M`, the
  uncorrected average of `L` is at least `2π + η`;
* `hsmall` – for every connected proper subset of size less than `M`, the
  corrected average exceeds `2π`;
* `hDelta_nonneg` – the boundary correction is nonnegative on all subsets.

**Conclusion** – `C` holds.
-/
theorem lower_average_character_criterion
    (vertices : Finset V) (L : V → ℝ) (Delta B : Finset V → ℝ) (chi : ℝ)
    (C : Prop) (η : ℝ) (M : ℕ)
    (IsConnected : Finset V → Prop)
    (comp : ConnectedComponentFamily vertices B IsConnected)
    (hobstruction :
      ∀ I : Finset V, I.Nonempty → I ⊆ vertices → I ≠ vertices →
        B I = (I.card : ℝ) * (correctedAverage L Delta I - 2 * Real.pi))
    (hchow :
      chi < 0 →
        (∀ I : Finset V, I.Nonempty → I ⊆ vertices → I ≠ vertices → 0 < B I) →
        C)
    (hchi : chi < 0)
    (hlarge :
      ∀ (I : Finset V), I.Nonempty → I ⊆ vertices → I ≠ vertices →
        IsConnected I →
        M ≤ I.card →
        2 * Real.pi + η ≤ correctedAverage L (fun _ => 0) I)
    (hsmall :
      ∀ (I : Finset V), I.Nonempty → I ⊆ vertices → I ≠ vertices →
        IsConnected I →
        I.card < M →
        2 * Real.pi < correctedAverage L Delta I)
    (hDelta_nonneg : ∀ I : Finset V, 0 ≤ Delta I)
    (h_eta_pos : 0 < η)
    (_hM_pos : 0 < M) :
    C := by
  apply hchow hchi
  intro I hI hsub hproper
  -- Decompose I into connected components.
  let comps := comp.components I hI hsub hproper
  have hcomps_nonempty : comps.Nonempty := by
    have hunion : I = comps.biUnion id := comp.component_union I hI hsub hproper
    rcases hI with ⟨x, hx⟩
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hx_union : x ∈ comps.biUnion id := by
      simpa [hunion] using hx
    simp [h] at hx_union
  -- For each component, prove B(J) > 0.
  have hB_components_pos :
      ∀ J ∈ comps, 0 < B J := by
    intro J hJ
    have hJ_ne : J.Nonempty := comp.component_nonempty I hI hsub hproper J hJ
    have hJ_sub_I : J ⊆ I := comp.component_subset I hI hsub hproper J hJ
    have hJ_sub_vertices : J ⊆ vertices := comp.component_subset_vertices I hI hsub hproper J hJ
    have hJ_connected : IsConnected J := comp.component_connected I hI hsub hproper J hJ
    have hJ_proper : J ≠ vertices := by
      intro hJ_eq
      have hvertices_sub_I : vertices ⊆ I := by
        intro x hx
        exact hJ_sub_I (by simpa [hJ_eq] using hx)
      exact hproper (Finset.Subset.antisymm hsub hvertices_sub_I)
    by_cases hsize : M ≤ J.card
    · -- Large component: use the uncorrected lower average.
      have hlower := hlarge J hJ_ne hJ_sub_vertices hJ_proper hJ_connected hsize
      have hcard_pos : 0 < (J.card : ℝ) := by
        exact_mod_cast (Finset.card_pos.mpr hJ_ne)
      have huncorr_le_corr :
          correctedAverage L (fun _ => 0) J ≤ correctedAverage L Delta J := by
        rw [correctedAverage]
        apply div_le_div_of_nonneg_right
        · simp [hDelta_nonneg J]
        · exact le_of_lt hcard_pos
      have hac_J : 2 * Real.pi < correctedAverage L Delta J := by
        linarith
      exact obstruction_pos_of_correctedAverage_gt L Delta B hJ_ne
        (hobstruction J hJ_ne hJ_sub_vertices hJ_proper) hac_J
    · -- Small component: use the corrected average hypothesis directly.
      have hsize' : J.card < M := by
        omega
      have hac_J := hsmall J hJ_ne hJ_sub_vertices hJ_proper hJ_connected hsize'
      exact obstruction_pos_of_correctedAverage_gt L Delta B hJ_ne
        (hobstruction J hJ_ne hJ_sub_vertices hJ_proper) hac_J
  -- Additivity of B gives B(I) > 0.
  rw [comp.B_add I hI hsub hproper]
  exact sum_pos_of_forall_pos comps (fun J => B J) hcomps_nonempty hB_components_pos

end LowerAverageCriterion

end

end ProbabilityCharacter
