import Mathlib

/-!
# Real inequalities for the Ge--Lin improvement note

This file formalizes the real-variable part of
`Ge_Lin_improvement_strict_proof.tex`.  The names use ASCII identifiers so the
file remains easy to import from ordinary Lean projects.
-/

namespace MathTheoremProject.GeLinImprovement

noncomputable section

/-- The cosine term of one Euclidean unit packing angle. -/
def triCos (a b c : Real) : Real :=
  (1 + a + b - c) / (2 * Real.sqrt (1 + a) * Real.sqrt (1 + b))

/-- First endpoint term in the box estimate for `triCos`. -/
def Q1 (xi eta : Real) : Real :=
  (1 + 2 * eta - xi) / (2 * (1 + eta))

/-- Second endpoint term in the box estimate for `triCos`. -/
def Q2 (xi eta : Real) : Real :=
  (1 / 2 : Real) * Real.sqrt ((1 + eta) / (1 + xi))

/-- The local box bound used in the proof note. -/
def Q (xi eta : Real) : Real :=
  max (Q1 xi eta) (Q2 xi eta)

/-- For fixed `B`, the auxiliary expression is bounded by its left endpoint
when `A` lies to the left of the critical point. -/
lemma oneVar_left_endpoint_bound
    {D A B : Real} (hDpos : 0 < D) (hApos : 0 < A) (hBpos : 0 < B)
    (hDleA : D <= A) (hAle : A <= B - D) :
    (A + B - D) / (2 * Real.sqrt A * Real.sqrt B) <=
      B / (2 * Real.sqrt D * Real.sqrt B) := by
  refine le_of_sq_le_sq ?hsq ?hrhs
  · rw [div_pow, div_pow]
    have hsA : Real.sqrt A ^ 2 = A := by rw [Real.sq_sqrt]; linarith
    have hsB : Real.sqrt B ^ 2 = B := by rw [Real.sq_sqrt]; linarith
    have hsD : Real.sqrt D ^ 2 = D := by rw [Real.sq_sqrt]; linarith
    field_simp [hApos.ne', hBpos.ne', hDpos.ne',
      ne_of_gt (Real.sqrt_pos_of_pos hApos),
      ne_of_gt (Real.sqrt_pos_of_pos hBpos),
      ne_of_gt (Real.sqrt_pos_of_pos hDpos)]
    have hnon : 0 <= A - D := by linarith
    have hB2D : 0 <= B - 2 * D := by linarith
    have hBD : 0 <= B - D := by linarith
    have hprodBD : 0 <= (B - D) * (B - 2 * D) := mul_nonneg hBD hB2D
    have hinner : 0 <= B ^ 2 - 2 * D * B - D * (A - D) := by
      nlinarith [hprodBD, hDpos, hAle]
    have hprod : 0 <= (A - D) * (B ^ 2 - 2 * D * B - D * (A - D)) :=
      mul_nonneg hnon hinner
    nlinarith [hsA, hsB, hsD, hprod]
  · positivity

/-- For fixed `B`, the auxiliary expression is bounded by its right endpoint
when `A` lies to the right of the critical point. -/
lemma oneVar_right_endpoint_bound
    {D E A B : Real} (hApos : 0 < A) (hBpos : 0 < B) (hEpos : 0 < E)
    (hAleE : A <= E) (hDleB : D <= B) (hcrit : B - D <= A) :
    (A + B - D) / (2 * Real.sqrt A * Real.sqrt B) <=
      (E + B - D) / (2 * Real.sqrt E * Real.sqrt B) := by
  refine le_of_sq_le_sq ?hsq ?hrhs
  · rw [div_pow, div_pow]
    have hsA : Real.sqrt A ^ 2 = A := by rw [Real.sq_sqrt]; linarith
    have hsB : Real.sqrt B ^ 2 = B := by rw [Real.sq_sqrt]; linarith
    have hsE : Real.sqrt E ^ 2 = E := by rw [Real.sq_sqrt]; linarith
    field_simp [hApos.ne', hBpos.ne', hEpos.ne',
      ne_of_gt (Real.sqrt_pos_of_pos hApos),
      ne_of_gt (Real.sqrt_pos_of_pos hBpos),
      ne_of_gt (Real.sqrt_pos_of_pos hEpos)]
    have hEA : 0 <= E - A := by linarith
    have hprod : 0 <= (A - (B - D)) * (E - (B - D)) :=
      mul_nonneg (by linarith) (by linarith)
    have hAE : (B - D) ^ 2 <= A * E := by nlinarith [hprod]
    have hfinal : 0 <= (E - A) * (A * E - (B - D) ^ 2) :=
      mul_nonneg hEA (by nlinarith)
    nlinarith [hsA, hsB, hsE, hfinal]
  · exact div_nonneg (by linarith) (by positivity)

/-- For fixed `B`, the maximum on `[D,E]` is attained at an endpoint. -/
lemma oneVar_endpoint_bound
    {D E A B : Real} (hDpos : 0 < D) (hApos : 0 < A) (hBpos : 0 < B)
    (hEpos : 0 < E) (hDleA : D <= A) (hAleE : A <= E) (hDleB : D <= B) :
    (A + B - D) / (2 * Real.sqrt A * Real.sqrt B) <=
      max (B / (2 * Real.sqrt D * Real.sqrt B))
        ((E + B - D) / (2 * Real.sqrt E * Real.sqrt B)) := by
  by_cases hcrit : A <= B - D
  · exact (oneVar_left_endpoint_bound hDpos hApos hBpos hDleA hcrit).trans
      (le_max_left _ _)
  · have hcrit' : B - D <= A := by linarith
    exact (oneVar_right_endpoint_bound hApos hBpos hEpos hAleE hDleB hcrit').trans
      (le_max_right _ _)

/-- The left endpoint is controlled by the square-root endpoint `Q2`. -/
lemma left_endpoint_le_sqrt_bound
    {D E B : Real} (hDpos : 0 < D) (hBpos : 0 < B) (hBleE : B <= E) :
    B / (2 * Real.sqrt D * Real.sqrt B) <=
      (1 / 2 : Real) * Real.sqrt (E / D) := by
  have hEpos : 0 < E := lt_of_lt_of_le hBpos hBleE
  refine le_of_sq_le_sq ?hsq ?hrhs
  · rw [div_pow, mul_pow]
    have hsD : Real.sqrt D ^ 2 = D := by rw [Real.sq_sqrt]; linarith
    have hsB : Real.sqrt B ^ 2 = B := by rw [Real.sq_sqrt]; linarith
    have hEDnon : 0 <= E / D := div_nonneg (le_of_lt hEpos) (le_of_lt hDpos)
    have hsED : Real.sqrt (E / D) ^ 2 = E / D := by rw [Real.sq_sqrt hEDnon]
    field_simp [hDpos.ne', hBpos.ne',
      ne_of_gt (Real.sqrt_pos_of_pos hDpos),
      ne_of_gt (Real.sqrt_pos_of_pos hBpos)]
    rw [hsD, hsB, hsED]
    field_simp [hDpos.ne']
    nlinarith [hBleE, hBpos]
  · positivity

/--
Lean version of Lemma 2.1 in the TeX note:
on the box `[xi, eta]^3`, the one-triangle cosine term is bounded by `Q xi eta`.
-/
lemma triCos_le_Q_of_mem_Icc
    {xi eta a b c : Real}
    (hxi_nonneg : 0 <= xi) (hxieta : xi <= eta) (_heta_le_one : eta <= 1)
    (ha : a ∈ Set.Icc xi eta) (hb : b ∈ Set.Icc xi eta) (hc : c ∈ Set.Icc xi eta) :
    triCos a b c <= Q xi eta := by
  let D : Real := 1 + xi
  let E : Real := 1 + eta
  let A : Real := 1 + a
  let B : Real := 1 + b
  have hDpos : 0 < D := by dsimp [D]; linarith
  have hEpos : 0 < E := by dsimp [E]; linarith
  have hApos : 0 < A := by dsimp [A]; linarith [ha.1, hxi_nonneg]
  have hBpos : 0 < B := by dsimp [B]; linarith [hb.1, hxi_nonneg]
  have hDleA : D <= A := by dsimp [D, A]; linarith [ha.1]
  have hAleE : A <= E := by dsimp [A, E]; linarith [ha.2]
  have hDleB : D <= B := by dsimp [D, B]; linarith [hb.1]
  have hBleE : B <= E := by dsimp [B, E]; linarith [hb.2]
  have hden_nonneg : 0 <= 2 * Real.sqrt (1 + a) * Real.sqrt (1 + b) := by
    positivity
  have h_c_step :
      triCos a b c <= (1 + a + b - xi) /
        (2 * Real.sqrt (1 + a) * Real.sqrt (1 + b)) := by
    unfold triCos
    exact div_le_div_of_nonneg_right (by linarith [hc.1]) hden_nonneg
  have hendpoint :
      (A + B - D) / (2 * Real.sqrt A * Real.sqrt B) <=
        max (B / (2 * Real.sqrt D * Real.sqrt B))
          ((E + B - D) / (2 * Real.sqrt E * Real.sqrt B)) :=
    oneVar_endpoint_bound hDpos hApos hBpos hEpos hDleA hAleE hDleB
  have hleftQ2 : B / (2 * Real.sqrt D * Real.sqrt B) <= Q2 xi eta := by
    have h := left_endpoint_le_sqrt_bound hDpos hBpos hBleE
    simpa [D, E, Q2, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h
  have hleftQ : B / (2 * Real.sqrt D * Real.sqrt B) <= Q xi eta := by
    exact hleftQ2.trans (by unfold Q; exact le_max_right _ _)
  have hright_endpoint_raw :
      (B + E - D) / (2 * Real.sqrt B * Real.sqrt E) <=
        max (E / (2 * Real.sqrt D * Real.sqrt E))
          ((E + E - D) / (2 * Real.sqrt E * Real.sqrt E)) :=
    oneVar_endpoint_bound hDpos hBpos hEpos hEpos hDleB hBleE (by linarith)
  have hright_endpoint :
      (E + B - D) / (2 * Real.sqrt E * Real.sqrt B) <=
        max (E / (2 * Real.sqrt D * Real.sqrt E))
          ((E + E - D) / (2 * Real.sqrt E * Real.sqrt E)) := by
    simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
      using hright_endpoint_raw
  have hrightLeftQ2 : E / (2 * Real.sqrt D * Real.sqrt E) <= Q2 xi eta := by
    have h := left_endpoint_le_sqrt_bound hDpos hEpos (le_rfl : E <= E)
    simpa [D, E, Q2, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h
  have hrightRightQ1 :
      (E + E - D) / (2 * Real.sqrt E * Real.sqrt E) <= Q1 xi eta := by
    have hsE : Real.sqrt E * Real.sqrt E = E := by
      rw [← pow_two, Real.sq_sqrt]
      linarith
    calc
      (E + E - D) / (2 * Real.sqrt E * Real.sqrt E)
          = (E + E - D) / (2 * (Real.sqrt E * Real.sqrt E)) := by ring
      _ = (E + E - D) / (2 * E) := by rw [hsE]
      _ = Q1 xi eta := by
        unfold Q1
        field_simp [D, E, hEpos.ne']
        ring
      _ <= Q1 xi eta := le_rfl
  have hrightQ : (E + B - D) / (2 * Real.sqrt E * Real.sqrt B) <= Q xi eta := by
    have hmax :
        max (E / (2 * Real.sqrt D * Real.sqrt E))
          ((E + E - D) / (2 * Real.sqrt E * Real.sqrt E)) <= Q xi eta := by
      apply max_le
      · exact hrightLeftQ2.trans (by unfold Q; exact le_max_right _ _)
      · exact hrightRightQ1.trans (by unfold Q; exact le_max_left _ _)
    exact hright_endpoint.trans hmax
  have hmaxQ :
      max (B / (2 * Real.sqrt D * Real.sqrt B))
        ((E + B - D) / (2 * Real.sqrt E * Real.sqrt B)) <= Q xi eta :=
    max_le hleftQ hrightQ
  calc
    triCos a b c <= (1 + a + b - xi) /
        (2 * Real.sqrt (1 + a) * Real.sqrt (1 + b)) := h_c_step
    _ = (A + B - D) / (2 * Real.sqrt A * Real.sqrt B) := by
      simp [A, B, D]
      ring
    _ <= max (B / (2 * Real.sqrt D * Real.sqrt B))
          ((E + B - D) / (2 * Real.sqrt E * Real.sqrt B)) := hendpoint
    _ <= Q xi eta := hmaxQ

/-- Angle form of `triCos_le_Q_of_mem_Icc`, using the antitonicity of `arccos`. -/
lemma arccos_Q_le_arccos_triCos_of_mem_Icc
    {xi eta a b c : Real}
    (hxi_nonneg : 0 <= xi) (hxieta : xi <= eta) (heta_le_one : eta <= 1)
    (ha : a ∈ Set.Icc xi eta) (hb : b ∈ Set.Icc xi eta) (hc : c ∈ Set.Icc xi eta) :
    Real.arccos (Q xi eta) <= Real.arccos (triCos a b c) :=
  Real.arccos_le_arccos
    (triCos_le_Q_of_mem_Icc hxi_nonneg hxieta heta_le_one ha hb hc)

lemma sqrt_two_sq : (Real.sqrt 2 : Real) ^ 2 = 2 := by
  rw [Real.sq_sqrt]
  norm_num

lemma sqrt_two_pos : 0 < (Real.sqrt 2 : Real) := by
  positivity

lemma sqrt_two_lt_two : (Real.sqrt 2 : Real) < 2 := by
  nlinarith [sqrt_two_sq, le_of_lt sqrt_two_pos]

lemma two_sub_sqrt_two_pos : 0 < (2 : Real) - Real.sqrt 2 := by
  linarith [sqrt_two_lt_two]

lemma sqrt_two_lt_three_div_two : (Real.sqrt 2 : Real) < 3 / 2 := by
  nlinarith [sqrt_two_sq, le_of_lt sqrt_two_pos]

lemma sqrt_two_div_two_lt_one : Real.sqrt 2 / 2 < (1 : Real) := by
  nlinarith [sqrt_two_lt_two]

lemma sqrt_two_div_two_le_three_div_four : Real.sqrt 2 / 2 <= (3 : Real) / 4 := by
  nlinarith [le_of_lt sqrt_two_lt_three_div_two]

/-- The arbitrary-weight endpoint `xi = 0`, `eta = 1` gives `Q = 3 / 4`. -/
lemma Q_zero_one : Q 0 1 = (3 : Real) / 4 := by
  unfold Q Q1 Q2
  have hq1 : (1 + 2 * (1 : Real) - 0) / (2 * (1 + 1)) = (3 : Real) / 4 := by
    norm_num
  have hq2 :
      (1 / 2 : Real) * Real.sqrt ((1 + (1 : Real)) / (1 + 0)) =
        Real.sqrt 2 / 2 := by
    norm_num
    ring
  rw [hq1, hq2]
  exact max_eq_left sqrt_two_div_two_le_three_div_four

/-- Constant weights give the endpoint `Q(s,s) = 1 / 2`. -/
lemma Q_diag (s : Real) (hs : -1 < s) : Q s s = (1 : Real) / 2 := by
  unfold Q Q1 Q2
  have hpos : 0 < 1 + s := by linarith
  have h1 : (1 + 2 * s - s) / (2 * (1 + s)) = (1 : Real) / 2 := by
    field_simp [ne_of_gt hpos]
    ring
  have h2 :
      (1 / 2 : Real) * Real.sqrt ((1 + s) / (1 + s)) = (1 : Real) / 2 := by
    rw [show (1 + s) / (1 + s) = (1 : Real) by field_simp [ne_of_gt hpos],
      Real.sqrt_one]
    norm_num
  rw [h1, h2, max_self]

/--
The degree-eight interval condition makes the first endpoint term strictly
smaller than `sqrt 2 / 2`.
-/
lemma Q1_lt_sqrt_two_div_two_of_eta_lt
    {xi eta : Real}
    (heta_nonneg : 0 <= eta)
    (h : eta < (Real.sqrt 2 - 1 + xi) / (2 - Real.sqrt 2)) :
    Q1 xi eta < Real.sqrt 2 / 2 := by
  unfold Q1
  have hden : 0 < (2 : Real) - Real.sqrt 2 := two_sub_sqrt_two_pos
  have hcalc : (2 - Real.sqrt 2) * eta < Real.sqrt 2 - 1 + xi := by
    have hmul := mul_lt_mul_of_pos_left h hden
    field_simp [ne_of_gt hden] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hnum : 1 + 2 * eta - xi < Real.sqrt 2 * (1 + eta) := by
    nlinarith [hcalc]
  have h1pos : 0 < 1 + eta := by linarith
  have hden2 : 0 < 2 * (1 + eta) := by nlinarith
  calc
    (1 + 2 * eta - xi) / (2 * (1 + eta))
        < (Real.sqrt 2 * (1 + eta)) / (2 * (1 + eta)) :=
          div_lt_div_of_pos_right hnum hden2
    _ = Real.sqrt 2 / 2 := by field_simp [ne_of_gt h1pos]

/--
The second endpoint term is below `sqrt 2 / 2` whenever
`eta < 1 + 2 * xi`.
-/
lemma Q2_lt_sqrt_two_div_two_of_eta_lt_one_add_two_mul
    {xi eta : Real}
    (hxi_nonneg : 0 <= xi) (heta_nonneg : 0 <= eta)
    (h : eta < 1 + 2 * xi) :
    Q2 xi eta < Real.sqrt 2 / 2 := by
  unfold Q2
  have hden : 0 < 1 + xi := by linarith
  have hnum : 1 + eta < 2 * (1 + xi) := by nlinarith
  have hratio : (1 + eta) / (1 + xi) < 2 := by
    calc
      (1 + eta) / (1 + xi) < (2 * (1 + xi)) / (1 + xi) :=
        div_lt_div_of_pos_right hnum hden
      _ = 2 := by field_simp [ne_of_gt hden]
  have hratio_nonneg : 0 <= (1 + eta) / (1 + xi) := by
    positivity
  have hsqrt : Real.sqrt ((1 + eta) / (1 + xi)) < Real.sqrt 2 :=
    Real.sqrt_lt_sqrt hratio_nonneg hratio
  calc
    (1 / 2 : Real) * Real.sqrt ((1 + eta) / (1 + xi))
        < (1 / 2 : Real) * Real.sqrt 2 :=
          mul_lt_mul_of_pos_left hsqrt (by norm_num)
    _ = Real.sqrt 2 / 2 := by ring

/--
Under the usual local assumptions `0 <= xi <= eta <= 1`, the degree-eight
interval condition implies the auxiliary inequality needed for `Q2`.
-/
lemma degreeEight_interval_implies_eta_lt_one_add_two_mul_xi
    {xi eta : Real}
    (hxi_nonneg : 0 <= xi) (heta_le_one : eta <= 1)
    (h : eta < (Real.sqrt 2 - 1 + xi) / (2 - Real.sqrt 2)) :
    eta < 1 + 2 * xi := by
  if hxi_pos : 0 < xi then
    have h1 : (1 : Real) < 1 + 2 * xi := by nlinarith
    exact lt_of_le_of_lt heta_le_one h1
  else
    have hxi_eq : xi = 0 := by linarith
    subst xi
    have hden : 0 < (2 : Real) - Real.sqrt 2 := two_sub_sqrt_two_pos
    have hrhs_lt_one :
        (Real.sqrt 2 - 1 + (0 : Real)) / (2 - Real.sqrt 2) < 1 := by
      have hnum : Real.sqrt 2 - 1 < (1 : Real) * (2 - Real.sqrt 2) := by
        nlinarith [sqrt_two_lt_three_div_two]
      calc
        (Real.sqrt 2 - 1 + (0 : Real)) / (2 - Real.sqrt 2)
            < ((1 : Real) * (2 - Real.sqrt 2)) / (2 - Real.sqrt 2) :=
              div_lt_div_of_pos_right (by simpa using hnum) hden
        _ = 1 := by field_simp [ne_of_gt hden]
    linarith

/--
The Lean version of the key `d_i >= 8` algebraic claim:
the local interval condition forces `Q(xi, eta) < sqrt 2 / 2`.
-/
lemma Q_lt_sqrt_two_div_two_of_degreeEight_interval
    {xi eta : Real}
    (hxi_nonneg : 0 <= xi) (heta_nonneg : 0 <= eta) (heta_le_one : eta <= 1)
    (h : eta < (Real.sqrt 2 - 1 + xi) / (2 - Real.sqrt 2)) :
    Q xi eta < Real.sqrt 2 / 2 := by
  unfold Q
  apply max_lt
  · exact Q1_lt_sqrt_two_div_two_of_eta_lt heta_nonneg h
  · exact Q2_lt_sqrt_two_div_two_of_eta_lt_one_add_two_mul hxi_nonneg heta_nonneg
      (degreeEight_interval_implies_eta_lt_one_add_two_mul_xi hxi_nonneg heta_le_one h)

end

end MathTheoremProject.GeLinImprovement
