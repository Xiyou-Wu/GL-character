import ProbabilityCharacter.Basic

/-!
# Finite combinatorial model for subset bookkeeping

This file starts the combinatorial layer behind the obstruction identity.  The
definitions model triangular faces, edges, and the three face classes
`F_1(I)`, `F_2(I)`, and `F_3(I)`.  The first verified theorem proves the exact
algebraic obstruction identity once the finite incidence-counting identities
have been supplied.
-/

namespace ProbabilityCharacter
namespace Combinatorics

open scoped BigOperators

noncomputable section

variable {V : Type*}

/-- A triangular face, represented by its three vertices. -/
structure TriFace (V : Type*) where
  verts : Finset V
  card_verts : verts.card = 3
deriving DecidableEq

/-- An edge, represented by its two endpoints. -/
structure TriEdge (V : Type*) where
  verts : Finset V
  card_verts : verts.card = 2
deriving DecidableEq

namespace TriEdge

theorem ext {e₁ e₂ : TriEdge V} (h : e₁.verts = e₂.verts) : e₁ = e₂ := by
  cases e₁
  cases e₂
  simp_all

/-- The endpoint set map, as an embedding. -/
def vertsEmbedding : TriEdge V ↪ Finset V where
  toFun e := e.verts
  inj' _ _ h := ext h

end TriEdge

namespace TriFace

variable [DecidableEq V]

/-- The vertices of a face lying in a chosen vertex subset. -/
def verticesIn (I : Finset V) (f : TriFace V) : Finset V :=
  f.verts.filter fun v => v ∈ I

/-- The number of vertices of a face lying in a chosen vertex subset. -/
def countIn (I : Finset V) (f : TriFace V) : Nat :=
  (verticesIn I f).card

theorem countIn_le_three (I : Finset V) (f : TriFace V) :
    countIn I f ≤ 3 := by
  unfold countIn verticesIn
  rw [← f.card_verts]
  exact Finset.card_filter_le _ _

theorem countIn_eq_card_filter (I : Finset V) (f : TriFace V) :
    countIn I f = (f.verts.filter fun v => v ∈ I).card := rfl

/-- The two-element vertex subsets of `f` whose vertices lie in `I`. -/
def internalVertexPairs (I : Finset V) (f : TriFace V) : Finset (Finset V) :=
  (verticesIn I f).powersetCard 2

theorem card_internalVertexPairs (I : Finset V) (f : TriFace V) :
    (internalVertexPairs I f).card = Nat.choose (countIn I f) 2 := by
  simp [internalVertexPairs, countIn]

theorem choose_two_countIn_eq_piecewise (I : Finset V) (f : TriFace V) :
    Nat.choose (countIn I f) 2 =
      if countIn I f = 3 then 3 else if countIn I f = 2 then 1 else 0 := by
  set n := countIn I f
  have hn : n ≤ 3 := by
    simpa [n] using countIn_le_three I f
  have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by
    omega
  rcases hcases with h0 | h1 | h2 | h3
  · simp [n, h0]
  · simp [n, h1]
  · simp [n, h2]
  · simp [n, h3]

end TriFace

/-- A finite combinatorial triangulation model with vertex, edge, and face sets. -/
structure TriangulationModel (V : Type*) where
  vertices : Finset V
  edges : Finset (TriEdge V)
  faces : Finset (TriFace V)

namespace TriangulationModel

variable [DecidableEq V]

/-- Faces with exactly `m` vertices in `I`. -/
def facesWithCount (T : TriangulationModel V) (I : Finset V) (m : Nat) :
    Finset (TriFace V) :=
  T.faces.filter fun f => TriFace.countIn I f = m

/-- Faces with exactly one vertex in `I`. -/
def F1 (T : TriangulationModel V) (I : Finset V) : Finset (TriFace V) :=
  facesWithCount T I 1

/-- Faces with exactly two vertices in `I`. -/
def F2 (T : TriangulationModel V) (I : Finset V) : Finset (TriFace V) :=
  facesWithCount T I 2

/-- Faces with all three vertices in `I`. -/
def F3 (T : TriangulationModel V) (I : Finset V) : Finset (TriFace V) :=
  facesWithCount T I 3

theorem mem_facesWithCount_iff
    (T : TriangulationModel V) (I : Finset V) (m : Nat) (f : TriFace V) :
    f ∈ facesWithCount T I m ↔ f ∈ T.faces ∧ TriFace.countIn I f = m := by
  simp [facesWithCount]

theorem mem_F1_iff (T : TriangulationModel V) (I : Finset V) (f : TriFace V) :
    f ∈ F1 T I ↔ f ∈ T.faces ∧ TriFace.countIn I f = 1 := by
  simp [F1, facesWithCount]

theorem mem_F2_iff (T : TriangulationModel V) (I : Finset V) (f : TriFace V) :
    f ∈ F2 T I ↔ f ∈ T.faces ∧ TriFace.countIn I f = 2 := by
  simp [F2, facesWithCount]

theorem mem_F3_iff (T : TriangulationModel V) (I : Finset V) (f : TriFace V) :
    f ∈ F3 T I ↔ f ∈ T.faces ∧ TriFace.countIn I f = 3 := by
  simp [F3, facesWithCount]

/-- Edges whose endpoints both lie in `I`. -/
def internalEdges (T : TriangulationModel V) (I : Finset V) : Finset (TriEdge V) :=
  by
    classical
    exact T.edges.filter fun e => e.verts ⊆ I

/-- A face is incident to an edge when it contains both endpoints of the edge. -/
def edgeInFace (e : TriEdge V) (f : TriFace V) : Prop :=
  e.verts ⊆ f.verts

/-- Faces incident to a given edge. -/
def incidentFaces (T : TriangulationModel V) (e : TriEdge V) : Finset (TriFace V) :=
  by
    classical
    exact T.faces.filter fun f => edgeInFace e f

/-- Internal edges of `I` that are contained in a fixed face. -/
def internalEdgesInFace
    (T : TriangulationModel V) (I : Finset V) (f : TriFace V) : Finset (TriEdge V) :=
  by
    classical
    exact internalEdges T I |>.filter fun e => edgeInFace e f

/--
The endpoint sets of the internal edges of `I` contained in `f`.
This is the bridge to the two-element subsets of `f ∩ I`.
-/
def internalEdgeVertexSetsInFace
    (T : TriangulationModel V) (I : Finset V) (f : TriFace V) : Finset (Finset V) :=
  (internalEdgesInFace T I f).map TriEdge.vertsEmbedding

theorem mem_internalEdges_iff
    (T : TriangulationModel V) (I : Finset V) (e : TriEdge V) :
    e ∈ internalEdges T I ↔ e ∈ T.edges ∧ e.verts ⊆ I := by
  simp [internalEdges]

omit [DecidableEq V] in
theorem mem_incidentFaces_iff
    (T : TriangulationModel V) (e : TriEdge V) (f : TriFace V) :
    f ∈ incidentFaces T e ↔ f ∈ T.faces ∧ edgeInFace e f := by
  simp [incidentFaces, edgeInFace]

theorem mem_internalEdgesInFace_iff
    (T : TriangulationModel V) (I : Finset V) (f : TriFace V) (e : TriEdge V) :
    e ∈ internalEdgesInFace T I f ↔ e ∈ internalEdges T I ∧ edgeInFace e f := by
  simp [internalEdgesInFace, edgeInFace]

theorem card_internalEdgeVertexSetsInFace
    (T : TriangulationModel V) (I : Finset V) (f : TriFace V) :
    (internalEdgeVertexSetsInFace T I f).card = (internalEdgesInFace T I f).card := by
  simp [internalEdgeVertexSetsInFace]

theorem internalEdgesInFace_card_eq_choose_of_vertexSet_image
    (T : TriangulationModel V) (I : Finset V) (f : TriFace V)
    (himage :
      internalEdgeVertexSetsInFace T I f = TriFace.internalVertexPairs I f) :
    (internalEdgesInFace T I f).card = Nat.choose (TriFace.countIn I f) 2 := by
  rw [← card_internalEdgeVertexSetsInFace T I f, himage,
    TriFace.card_internalVertexPairs]

/-- The incidence count summed by internal edges. -/
def edgeSideIncidenceCount (T : TriangulationModel V) (I : Finset V) : Nat :=
  ∑ e ∈ internalEdges T I, (incidentFaces T e).card

/-- The incidence count summed by faces. -/
def faceSideIncidenceCount (T : TriangulationModel V) (I : Finset V) : Nat :=
  ∑ f ∈ T.faces, (internalEdgesInFace T I f).card

/-- The global finite relation of internal edges of `I` incident to faces. -/
def edgeFaceIncidences (T : TriangulationModel V) (I : Finset V) :
    Finset (TriEdge V × TriFace V) :=
  by
    classical
    exact (internalEdges T I ×ˢ T.faces).filter fun p => edgeInFace p.1 p.2

theorem edgeFaceIncidences_card_eq_edgeSideIncidenceCount
    (T : TriangulationModel V) (I : Finset V) :
    (edgeFaceIncidences T I).card = edgeSideIncidenceCount T I := by
  unfold edgeFaceIncidences edgeSideIncidenceCount incidentFaces
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl ?_
  intro e he
  rw [Finset.card_filter]

theorem edgeFaceIncidences_card_eq_faceSideIncidenceCount
    (T : TriangulationModel V) (I : Finset V) :
    (edgeFaceIncidences T I).card = faceSideIncidenceCount T I := by
  unfold edgeFaceIncidences faceSideIncidenceCount internalEdgesInFace
  rw [Finset.card_filter, Finset.sum_product_right]
  refine Finset.sum_congr rfl ?_
  intro f hf
  rw [Finset.card_filter]

theorem edgeSideIncidenceCount_eq_faceSideIncidenceCount
    (T : TriangulationModel V) (I : Finset V) :
    edgeSideIncidenceCount T I = faceSideIncidenceCount T I := by
  rw [← edgeFaceIncidences_card_eq_edgeSideIncidenceCount,
    edgeFaceIncidences_card_eq_faceSideIncidenceCount]

theorem sum_ite_three_eq_three_mul_card_filter
    {α : Type*} (s : Finset α) (p : α -> Prop) [DecidablePred p] :
    (∑ x ∈ s, if p x then 3 else 0 : Nat) = 3 * (s.filter p).card := by
  calc
    (∑ x ∈ s, if p x then 3 else 0 : Nat)
        = ∑ x ∈ s, 3 * (if p x then 1 else 0 : Nat) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          by_cases hp : p x <;> simp [hp]
    _ = 3 * (∑ x ∈ s, if p x then 1 else 0 : Nat) := by
          rw [Finset.mul_sum]
    _ = 3 * (s.filter p).card := by
          rw [Finset.sum_boole]
          simp

theorem sum_ite_one_eq_card_filter
    {α : Type*} (s : Finset α) (p : α -> Prop) [DecidablePred p] :
    (∑ x ∈ s, if p x then 1 else 0 : Nat) = (s.filter p).card := by
  rw [Finset.sum_boole]
  simp

theorem faceSideIncidenceCount_eq_three_mul_F3_add_F2_of_face_contribution
    (T : TriangulationModel V) (I : Finset V)
    (hface : ∀ f ∈ T.faces,
      (internalEdgesInFace T I f).card =
        if TriFace.countIn I f = 3 then 3
        else if TriFace.countIn I f = 2 then 1
        else 0) :
    faceSideIncidenceCount T I = 3 * (F3 T I).card + (F2 T I).card := by
  unfold faceSideIncidenceCount F2 F3 facesWithCount
  calc
    (∑ f ∈ T.faces, (internalEdgesInFace T I f).card)
        = ∑ f ∈ T.faces,
            (if TriFace.countIn I f = 3 then 3
              else if TriFace.countIn I f = 2 then 1
              else 0) := by
          refine Finset.sum_congr rfl ?_
          intro f hf
          exact hface f hf
    _ = ∑ f ∈ T.faces,
            ((if TriFace.countIn I f = 3 then 3 else 0) +
              (if TriFace.countIn I f = 2 then 1 else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro f hf
          by_cases h3 : TriFace.countIn I f = 3
          · simp [h3]
          · by_cases h2 : TriFace.countIn I f = 2 <;> simp [h3, h2]
    _ = (∑ f ∈ T.faces, if TriFace.countIn I f = 3 then 3 else 0) +
          (∑ f ∈ T.faces, if TriFace.countIn I f = 2 then 1 else 0) := by
          rw [Finset.sum_add_distrib]
    _ = 3 * (T.faces.filter fun f => TriFace.countIn I f = 3).card +
          (T.faces.filter fun f => TriFace.countIn I f = 2).card := by
          rw [sum_ite_three_eq_three_mul_card_filter,
            sum_ite_one_eq_card_filter]

theorem faceSideIncidenceCount_eq_three_mul_F3_add_F2_of_choose_contribution
    (T : TriangulationModel V) (I : Finset V)
    (hface : ∀ f ∈ T.faces,
      (internalEdgesInFace T I f).card = Nat.choose (TriFace.countIn I f) 2) :
    faceSideIncidenceCount T I = 3 * (F3 T I).card + (F2 T I).card := by
  exact faceSideIncidenceCount_eq_three_mul_F3_add_F2_of_face_contribution T I
    (fun f hf => by
      rw [hface f hf, TriFace.choose_two_countIn_eq_piecewise])


theorem edgeSideIncidenceCount_eq_two_mul
    (T : TriangulationModel V) (I : Finset V)
    (hclosed : ∀ e ∈ internalEdges T I, (incidentFaces T e).card = 2) :
    edgeSideIncidenceCount T I = 2 * (internalEdges T I).card := by
  unfold edgeSideIncidenceCount
  calc
    (∑ e ∈ internalEdges T I, (incidentFaces T e).card)
        = ∑ _e ∈ internalEdges T I, 2 := by
          refine Finset.sum_congr rfl ?_
          intro e he
          exact hclosed e he
    _ = (internalEdges T I).card * 2 := by
          simp
    _ = 2 * (internalEdges T I).card := by
          omega

/--
The finite incidence-counting statement used in the paper:
`2 |E_I| = 3 |F_3(I)| + |F_2(I)|`.
-/
def subsetEdgeCountIdentity (T : TriangulationModel V) (I : Finset V) : Prop :=
  2 * (internalEdges T I).card = 3 * (F3 T I).card + (F2 T I).card

/-- Euler characteristic of the full subcomplex induced by `I`, from counts. -/
def subsetEulerCount (T : TriangulationModel V) (I : Finset V) : ℝ :=
  (I.card : ℝ) - ((internalEdges T I).card : ℝ) + ((F3 T I).card : ℝ)

theorem subsetEdgeCountIdentity_of_incidence_counts
    (T : TriangulationModel V) (I : Finset V)
    (hclosed : ∀ e ∈ internalEdges T I, (incidentFaces T e).card = 2)
    (hdouble : edgeSideIncidenceCount T I = faceSideIncidenceCount T I)
    (hfaces :
      faceSideIncidenceCount T I = 3 * (F3 T I).card + (F2 T I).card) :
    subsetEdgeCountIdentity T I := by
  unfold subsetEdgeCountIdentity
  rw [← hfaces, ← hdouble, edgeSideIncidenceCount_eq_two_mul T I hclosed]

theorem subsetEdgeCountIdentity_of_face_side_count
    (T : TriangulationModel V) (I : Finset V)
    (hclosed : ∀ e ∈ internalEdges T I, (incidentFaces T e).card = 2)
    (hfaces :
      faceSideIncidenceCount T I = 3 * (F3 T I).card + (F2 T I).card) :
    subsetEdgeCountIdentity T I := by
  exact subsetEdgeCountIdentity_of_incidence_counts T I hclosed
    (edgeSideIncidenceCount_eq_faceSideIncidenceCount T I) hfaces

theorem subsetEdgeCountIdentity_of_local_face_contribution
    (T : TriangulationModel V) (I : Finset V)
    (hclosed : ∀ e ∈ internalEdges T I, (incidentFaces T e).card = 2)
    (hface : ∀ f ∈ T.faces,
      (internalEdgesInFace T I f).card =
        if TriFace.countIn I f = 3 then 3
        else if TriFace.countIn I f = 2 then 1
        else 0) :
    subsetEdgeCountIdentity T I := by
  exact subsetEdgeCountIdentity_of_face_side_count T I hclosed
    (faceSideIncidenceCount_eq_three_mul_F3_add_F2_of_face_contribution T I hface)

theorem subsetEdgeCountIdentity_of_choose_face_contribution
    (T : TriangulationModel V) (I : Finset V)
    (hclosed : ∀ e ∈ internalEdges T I, (incidentFaces T e).card = 2)
    (hface : ∀ f ∈ T.faces,
      (internalEdgesInFace T I f).card = Nat.choose (TriFace.countIn I f) 2) :
    subsetEdgeCountIdentity T I := by
  exact subsetEdgeCountIdentity_of_face_side_count T I hclosed
    (faceSideIncidenceCount_eq_three_mul_F3_add_F2_of_choose_contribution T I hface)

theorem subsetEdgeCountIdentity_of_internalEdgeVertexSet_images
    (T : TriangulationModel V) (I : Finset V)
    (hclosed : ∀ e ∈ internalEdges T I, (incidentFaces T e).card = 2)
    (himage : ∀ f ∈ T.faces,
      internalEdgeVertexSetsInFace T I f = TriFace.internalVertexPairs I f) :
    subsetEdgeCountIdentity T I := by
  exact subsetEdgeCountIdentity_of_choose_face_contribution T I hclosed
    (fun f hf => internalEdgesInFace_card_eq_choose_of_vertexSet_image T I f
      (himage f hf))

end TriangulationModel

/--
The obstruction identity follows from the finite counting identities and the
collapsed character-plus-correction formula.
-/
theorem obstruction_identity_from_count_data
    (vertexCount edgeCount F2Count F3Count : Nat)
    (L Delta B chi linkSum : ℝ)
    (hEdge : 2 * (edgeCount : ℝ) = 3 * (F3Count : ℝ) + (F2Count : ℝ))
    (hChi : chi = (vertexCount : ℝ) - (edgeCount : ℝ) + (F3Count : ℝ))
    (hLDelta :
      L + Delta =
        Real.pi * (F3Count : ℝ) + Real.pi * (F2Count : ℝ) + linkSum)
    (hB : B = linkSum - 2 * Real.pi * chi) :
    B = L - 2 * Real.pi * (vertexCount : ℝ) + Delta := by
  have hEdgePi :
      2 * Real.pi * (edgeCount : ℝ) =
        3 * Real.pi * (F3Count : ℝ) + Real.pi * (F2Count : ℝ) := by
    have h := congrArg (fun x : ℝ => Real.pi * x) hEdge
    nlinarith [h]
  have hEdgeSurplus :
      2 * Real.pi * (edgeCount : ℝ) - 2 * Real.pi * (F3Count : ℝ) =
        Real.pi * (F3Count : ℝ) + Real.pi * (F2Count : ℝ) := by
    nlinarith [hEdgePi]
  rw [hB, hChi]
  calc
    linkSum - 2 * Real.pi *
        ((vertexCount : ℝ) - (edgeCount : ℝ) + (F3Count : ℝ))
        = linkSum - 2 * Real.pi * (vertexCount : ℝ) +
            (2 * Real.pi * (edgeCount : ℝ) - 2 * Real.pi * (F3Count : ℝ)) := by
          ring
    _ = linkSum - 2 * Real.pi * (vertexCount : ℝ) +
            (Real.pi * (F3Count : ℝ) + Real.pi * (F2Count : ℝ)) := by
          rw [hEdgeSurplus]
    _ = (Real.pi * (F3Count : ℝ) + Real.pi * (F2Count : ℝ) + linkSum) -
            2 * Real.pi * (vertexCount : ℝ) := by
          ring
    _ = (L + Delta) - 2 * Real.pi * (vertexCount : ℝ) := by
          rw [← hLDelta]
    _ = L - 2 * Real.pi * (vertexCount : ℝ) + Delta := by
          ring

end

end Combinatorics
end ProbabilityCharacter
