import MathTheoremProject.GeLinImprovement.RealInequalities

/-!
# Finite-sum character criteria

These lemmas isolate the finite summation step used to pass from local
one-triangle angle estimates to `L_i > 2 * pi`.
-/

namespace MathTheoremProject.GeLinImprovement

open scoped BigOperators

noncomputable section

/--
If every term in a finite family is at least `theta` and
`card * theta > target`, then the sum is greater than `target`.
-/
theorem sum_gt_of_card_mul_lower_bound
    {alpha : Type*} [Fintype alpha]
    (gamma : alpha -> Real) (theta target : Real)
    (hgamma : forall x, theta <= gamma x)
    (hcard : (Fintype.card alpha : Real) * theta > target) :
    Finset.univ.sum gamma > target := by
  have hsum : (Fintype.card alpha : Real) * theta <= Finset.univ.sum gamma := by
    calc
      (Fintype.card alpha : Real) * theta =
          Finset.univ.sum (fun _ : alpha => theta) := by
        simp
      _ <= Finset.univ.sum gamma :=
        Finset.sum_le_sum (by intro x hx; exact hgamma x)
  exact lt_of_lt_of_le hcard hsum

/--
Strict lower bounds are enough when `card * theta` only reaches the target.
This is the form used for `d >= 8` and `theta = pi / 4`.
-/
theorem fin_sum_gt_of_strict_lower_bound
    {d : Nat} (hd : 0 < d) (gamma : Fin d -> Real) (theta target : Real)
    (hgamma : forall x, theta < gamma x)
    (hcard : target <= (d : Real) * theta) :
    target < Finset.univ.sum gamma := by
  letI : Nonempty (Fin d) := Nonempty.intro (Fin.mk 0 hd)
  have hconst_lt :
      Finset.univ.sum (fun _ : Fin d => theta) < Finset.univ.sum gamma :=
    Finset.sum_lt_sum_of_nonempty
      (s := Finset.univ) (f := fun _ : Fin d => theta) (g := gamma)
      Finset.univ_nonempty
      (by intro x hx; exact hgamma x)
  have hconst_eq : Finset.univ.sum (fun _ : Fin d => theta) = (d : Real) * theta := by
    simp
  rw [hconst_eq] at hconst_lt
  exact lt_of_le_of_lt hcard hconst_lt

/--
The finite-sum step in the degree-eight criterion:
`d >= 8` angles, each strictly larger than `pi / 4`, sum to more than `2*pi`.
-/
theorem eight_angle_sum_gt_two_pi
    {d : Nat} (hd8 : 8 <= d) (gamma : Fin d -> Real)
    (hgamma : forall x, Real.pi / 4 < gamma x) :
    2 * Real.pi < Finset.univ.sum gamma := by
  have hdpos : 0 < d := Nat.lt_of_lt_of_le (by norm_num) hd8
  apply fin_sum_gt_of_strict_lower_bound hdpos gamma (Real.pi / 4) (2 * Real.pi) hgamma
  have hdreal : (8 : Real) <= d := by exact_mod_cast hd8
  nlinarith [Real.pi_pos]

/--
An abstract Lean wrapper for the degree-eight local proof.

`cosTerm` is the one-triangle cosine expression, and `gamma` is the
corresponding angle contribution.  The final hypothesis is the monotonicity
input supplied in the paper by `gamma = arccos cosTerm`.
-/
theorem degreeEight_character_gt_two_pi
    {d : Nat} (hd8 : 8 <= d)
    {xi eta : Real}
    (hxi_nonneg : 0 <= xi) (heta_nonneg : 0 <= eta) (heta_le_one : eta <= 1)
    (hinterval : eta < (Real.sqrt 2 - 1 + xi) / (2 - Real.sqrt 2))
    (cosTerm gamma : Fin d -> Real)
    (hcos_le_Q : forall t, cosTerm t <= Q xi eta)
    (hangle_of_cos_lt : forall t, cosTerm t < Real.sqrt 2 / 2 -> Real.pi / 4 < gamma t) :
    2 * Real.pi < Finset.univ.sum gamma := by
  have hQ : Q xi eta < Real.sqrt 2 / 2 :=
    Q_lt_sqrt_two_div_two_of_degreeEight_interval
      hxi_nonneg heta_nonneg heta_le_one hinterval
  apply eight_angle_sum_gt_two_pi hd8 gamma
  intro t
  exact hangle_of_cos_lt t (lt_of_le_of_lt (hcos_le_Q t) hQ)

end

end MathTheoremProject.GeLinImprovement
