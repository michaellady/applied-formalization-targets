import Applied.Statistics.NormalDensity

/-!
# A checkable table of the standard normal distribution function

A table assigns to each grid point `i / H` (`H = 1024`, `i ≤ imax`) four natural numbers:
lower and upper bounds, scaled by `D = 10^40`, for the upper tail `1 - Φ(i / H)` and for the
density `phi (i / H)`.

* `tableOK tab imax : Bool` checks a table using only natural-number arithmetic: the entry at
  `0` against `1/√(2π)` (through 20-digit bounds on `π`), consecutive densities against a cubic
  Taylor enclosure of `exp`, consecutive tails against the slice bounds of
  `Applied.Statistics.NormalDensity`, and the last tail against Mills' ratio.
* `valid_of_tableOK`: a table passing the check is correct.
* `tailUp`, `tailDown`, `PhiUp`, `PhiDown`: evaluation of the tail and of `Φ` at the points
  `y / (H R)` of a finer lattice (`R = 4096`), by one table look-up and a cubic correction;
  `PhiUp_spec`, `PhiDown_spec` prove that they enclose `D Φ(y / (H R))`.
-/

open MeasureTheory ProbabilityTheory
open scoped Real

namespace Applied.Statistics.NormalTable

local notation "Φ" => cdf (gaussianReal 0 1)

/-- Grid resolution of the table: the grid points are `i / H`. -/
def H : ℕ := 1024
/-- Sub-grid resolution: evaluation points are `y / (H * R)`. -/
def R : ℕ := 4096
/-- Fixed-point scale of the table entries. -/
def D : ℕ := 10 ^ 40
/-- `Q = H² R`. -/
def Q : ℕ := H * H * R
/-- Common denominator of the slice polynomials. -/
def slDen : ℕ := H * R * (6 * Q * Q)
/-- Numerator and denominator of rational bounds for `π`. -/
def piLo : ℕ := 314159265358979323846
def piHi : ℕ := 314159265358979323847
def piDen : ℕ := 10 ^ 20

/-- A table entry: bounds for `D (1 - Φ x)` and `D phi x`. -/
structure Entry where
  tailLo : ℕ
  tailHi : ℕ
  phiLo : ℕ
  phiHi : ℕ

/-- Correctness of an entry at the grid point `i / H`. -/
def Entry.Valid (e : Entry) (i : ℕ) : Prop :=
  (e.phiLo : ℝ) ≤ D * phi (i / H) ∧ (D : ℝ) * phi (i / H) ≤ e.phiHi ∧
    (e.tailLo : ℝ) ≤ D * (1 - Φ (i / H)) ∧ (D : ℝ) * (1 - Φ (i / H)) ≤ e.tailHi

/-- Numerator of the upper slice polynomial `δ + b δ²/2 + b² δ³/3`, `b = i/H`, `δ = d/(H R)`. -/
def slUp (i d : ℕ) : ℕ := d * (6 * Q * Q + 3 * i * d * Q + 2 * (i * d) ^ 2)
/-- Positive part of the numerator of the lower slice polynomial `δ + b δ²/2 - δ³/6`. -/
def slLoP (i d : ℕ) : ℕ := d * (6 * Q * Q + 3 * i * d * Q)
/-- Negative part of the numerator of the lower slice polynomial. -/
def slLoN (d : ℕ) : ℕ := d * (d * d * H * H)

/-- Check of the density recursion between the entries at `i` and `i + 1`. -/
def phiStepOK (e e' : Entry) (i : ℕ) : Bool :=
  let a := 2 * i + 1
  let B := 2 * H * H
  let P := 96 * B ^ 4 + 48 * a ^ 2 * B ^ 2
  let N := 96 * a * B ^ 3 + 16 * a ^ 3 * B
  decide (e.phiHi * (P + 5 * a ^ 4) ≤ e'.phiHi * (96 * B ^ 4) + e.phiHi * N) &&
    decide (e'.phiLo * (96 * B ^ 4) + e.phiLo * (N + 5 * a ^ 4) ≤ e.phiLo * P)

/-- Check of the tail recursion between the entries at `i` and `i + 1`. -/
def tailStepOK (e e' : Entry) (i : ℕ) : Bool :=
  decide (e'.tailHi * slDen + e'.phiHi * slUp (i + 1) R ≤ e.tailHi * slDen) &&
    decide (e.tailLo * slDen + e'.phiLo * slLoN R ≤ e'.tailLo * slDen + e'.phiLo * slLoP (i + 1) R)

/-- Check of the first entry (against `1/√(2π)`) and of the last one (Mills' ratio). -/
def baseOK (e0 emax : Entry) (imax : ℕ) : Bool :=
  decide (D * D * piDen ≤ e0.phiHi ^ 2 * (2 * piLo)) &&
    decide (e0.phiLo ^ 2 * (2 * piHi) ≤ D * D * piDen) &&
    decide (emax.phiHi * H ≤ emax.tailHi * imax) && decide (emax.tailLo = 0) &&
    decide (0 < imax) && decide (imax ≤ H * H)

/-- The complete check of a table. -/
def tableOK (tab : ℕ → Entry) (imax : ℕ) : Bool :=
  baseOK (tab 0) (tab imax) imax &&
    (List.range imax).all fun i =>
      phiStepOK (tab i) (tab (i + 1)) i && tailStepOK (tab i) (tab (i + 1)) i

lemma H_pos : (0 : ℝ) < H := by norm_num [H]
lemma R_pos : (0 : ℝ) < R := by norm_num [R]
lemma D_pos : (0 : ℝ) < D := by norm_num [D]
lemma Q_eq : (Q : ℝ) = H * H * R := by norm_num [Q]
lemma slDen_eq : (slDen : ℝ) = H * R * (6 * Q * Q) := by norm_num [slDen]
lemma slDen_pos : (0 : ℝ) < slDen := by norm_num [slDen, Q, H, R]

/-- The upper slice polynomial in integer form. -/
lemma slUp_eq (i d : ℕ) :
    ((d : ℝ) / (H * R)) + (i / H) * ((d : ℝ) / (H * R)) ^ 2 / 2
        + ((i : ℝ) / H) ^ 2 * ((d : ℝ) / (H * R)) ^ 3 / 3
      = slUp i d / slDen := by
  have hH := H_pos
  have hR := R_pos
  rw [slDen_eq]
  simp only [slUp, Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Q_eq]
  field_simp
  ring

/-- The lower slice polynomial in integer form. -/
lemma slLo_eq (i d : ℕ) :
    ((d : ℝ) / (H * R)) + (i / H) * ((d : ℝ) / (H * R)) ^ 2 / 2 - ((d : ℝ) / (H * R)) ^ 3 / 6
      = ((slLoP i d : ℝ) - slLoN d) / slDen := by
  have hH := H_pos
  have hR := R_pos
  rw [slDen_eq]
  simp only [slLoP, slLoN, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Q_eq]
  field_simp
  ring

/-- Slice enclosure from a valid entry: bounds for `D (Φ b - Φ (b - δ))` with `b = i / H` and
`δ = d / (H R)`. -/
lemma slice_bounds {e : Entry} {i d : ℕ} (hv : e.Valid i) (hid : i * d ≤ Q) :
    ((e.phiLo : ℝ) * (slLoP i d - slLoN d)) / slDen
        ≤ D * (Φ (i / H) - Φ (i / H - d / (H * R))) ∧
      (D : ℝ) * (Φ (i / H) - Φ (i / H - d / (H * R))) ≤ (e.phiHi : ℝ) * slUp i d / slDen := by
  have hH := H_pos
  have hR := R_pos
  have hD := D_pos
  have hδ : (0 : ℝ) ≤ (d : ℝ) / (H * R) := by positivity
  have hb : (0 : ℝ) ≤ (i : ℝ) / H := by positivity
  have hbδ : ((i : ℝ) / H) * ((d : ℝ) / (H * R)) ≤ 1 := by
    have h1 : ((i * d : ℕ) : ℝ) ≤ Q := by exact_mod_cast hid
    rw [Q_eq] at h1
    push_cast at h1
    rw [div_mul_div_comm, div_le_one (by positivity)]
    nlinarith
  obtain ⟨h1, h2, -, -⟩ := hv
  constructor
  · have hlow := cdf_slice_ge ((i : ℝ) / H) hδ
    rw [slLo_eq] at hlow
    by_cases hsign : (0 : ℝ) ≤ (slLoP i d : ℝ) - slLoN d
    · calc ((e.phiLo : ℝ) * (slLoP i d - slLoN d)) / slDen
          ≤ ((D : ℝ) * phi (i / H) * (slLoP i d - slLoN d)) / slDen := by
            gcongr
        _ = D * (phi (i / H) * (((slLoP i d : ℝ) - slLoN d) / slDen)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hlow hD.le
    · have hneg : ((e.phiLo : ℝ) * (slLoP i d - slLoN d)) / slDen ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (not_le.mp hsign).le) slDen_pos.le
      have hmono : Φ ((i : ℝ) / H - d / (H * R)) ≤ Φ (i / H) :=
        monotone_cdf _ (by linarith)
      have : (0 : ℝ) ≤ D * (Φ (i / H) - Φ (i / H - d / (H * R))) :=
        mul_nonneg hD.le (sub_nonneg.mpr hmono)
      linarith
  · have hup := cdf_slice_le hb hδ hbδ
    rw [slUp_eq] at hup
    calc (D : ℝ) * (Φ (i / H) - Φ (i / H - d / (H * R)))
        ≤ D * (phi (i / H) * (slUp i d / slDen)) := mul_le_mul_of_nonneg_left hup hD.le
      _ = (D * phi (i / H)) * slUp i d / slDen := by ring
      _ ≤ (e.phiHi : ℝ) * slUp i d / slDen := by gcongr

/-- The density part of validity propagates from `i` to `i + 1`. -/
lemma phi_step {e e' : Entry} {i : ℕ} (h1 : (e.phiLo : ℝ) ≤ D * phi (i / H))
    (h2 : (D : ℝ) * phi (i / H) ≤ e.phiHi) (hi : 2 * i + 1 ≤ 2 * H * H)
    (hok : phiStepOK e e' i = true) :
    (e'.phiLo : ℝ) ≤ D * phi ((i + 1 : ℕ) / H) ∧ (D : ℝ) * phi ((i + 1 : ℕ) / H) ≤ e'.phiHi := by
  have hH := H_pos
  have hD := D_pos
  simp only [phiStepOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hhi, hlo⟩ := hok
  have hhi' := (Nat.cast_le (α := ℝ)).mpr hhi
  have hlo' := (Nat.cast_le (α := ℝ)).mpr hlo
  push_cast at hhi' hlo'
  set a : ℝ := 2 * i + 1 with ha
  set B : ℝ := 2 * H * H with hB
  have hB0 : 0 < B := by positivity
  have ha0 : 0 ≤ a := by positivity
  have haB : a ≤ B := by
    have := (Nat.cast_le (α := ℝ)).mpr hi
    push_cast at this
    exact this
  set t : ℝ := a / B with ht
  have ht0 : 0 ≤ t := div_nonneg ha0 hB0.le
  have ht1 : t ≤ 1 := (div_le_one hB0).mpr haB
  have hphi : phi ((i + 1 : ℕ) / H) = phi (i / H) * Real.exp (-t) := by
    have : ((i + 1 : ℕ) : ℝ) / H = i / H + 1 / H := by push_cast; ring
    rw [this, phi_add]
    congr 2
    rw [ht, ha, hB]
    field_simp
  have hexp := abs_le.mp (abs_exp_neg_sub_le ht0 ht1)
  have hP : 1 - t + t ^ 2 / 2 - t ^ 3 / 6
      = (96 * B ^ 4 + 48 * a ^ 2 * B ^ 2 - (96 * a * B ^ 3 + 16 * a ^ 3 * B)) / (96 * B ^ 4) := by
    rw [ht]; field_simp; ring
  have ht4 : 5 / 96 * t ^ 4 = 5 * a ^ 4 / (96 * B ^ 4) := by
    rw [ht]; field_simp
  have hden : (0 : ℝ) < 96 * B ^ 4 := by positivity
  have hexp0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have hphi0 : 0 ≤ phi (i / H : ℝ) := (phi_pos _).le
  rw [hphi]
  constructor
  · -- lower bound
    have hE : (96 * B ^ 4 + 48 * a ^ 2 * B ^ 2 - (96 * a * B ^ 3 + 16 * a ^ 3 * B) - 5 * a ^ 4)
        / (96 * B ^ 4) ≤ Real.exp (-t) := by
      have := hexp.1
      rw [hP, ht4] at this
      have e : (96 * B ^ 4 + 48 * a ^ 2 * B ^ 2 - (96 * a * B ^ 3 + 16 * a ^ 3 * B) - 5 * a ^ 4)
          / (96 * B ^ 4) = (96 * B ^ 4 + 48 * a ^ 2 * B ^ 2 - (96 * a * B ^ 3 + 16 * a ^ 3 * B))
            / (96 * B ^ 4) - 5 * a ^ 4 / (96 * B ^ 4) := by ring
      rw [e]; linarith
    have h3 : (e'.phiLo : ℝ) ≤ e.phiLo * ((96 * B ^ 4 + 48 * a ^ 2 * B ^ 2
        - (96 * a * B ^ 3 + 16 * a ^ 3 * B) - 5 * a ^ 4) / (96 * B ^ 4)) := by
      rw [← mul_div_assoc, le_div_iff₀ hden]
      nlinarith
    calc (e'.phiLo : ℝ) ≤ e.phiLo * ((96 * B ^ 4 + 48 * a ^ 2 * B ^ 2
          - (96 * a * B ^ 3 + 16 * a ^ 3 * B) - 5 * a ^ 4) / (96 * B ^ 4)) := h3
      _ ≤ e.phiLo * Real.exp (-t) := mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg _)
      _ ≤ (D * phi (i / H)) * Real.exp (-t) := mul_le_mul_of_nonneg_right h1 hexp0
      _ = D * (phi (i / H) * Real.exp (-t)) := by ring
  · -- upper bound
    have hE : Real.exp (-t) ≤ (96 * B ^ 4 + 48 * a ^ 2 * B ^ 2
        - (96 * a * B ^ 3 + 16 * a ^ 3 * B) + 5 * a ^ 4) / (96 * B ^ 4) := by
      have := hexp.2
      rw [hP, ht4] at this
      have e : (96 * B ^ 4 + 48 * a ^ 2 * B ^ 2 - (96 * a * B ^ 3 + 16 * a ^ 3 * B) + 5 * a ^ 4)
          / (96 * B ^ 4) = (96 * B ^ 4 + 48 * a ^ 2 * B ^ 2 - (96 * a * B ^ 3 + 16 * a ^ 3 * B))
            / (96 * B ^ 4) + 5 * a ^ 4 / (96 * B ^ 4) := by ring
      rw [e]; linarith
    have h3 : (e.phiHi : ℝ) * ((96 * B ^ 4 + 48 * a ^ 2 * B ^ 2
        - (96 * a * B ^ 3 + 16 * a ^ 3 * B) + 5 * a ^ 4) / (96 * B ^ 4)) ≤ e'.phiHi := by
      rw [← mul_div_assoc, div_le_iff₀ hden]
      nlinarith
    calc (D : ℝ) * (phi (i / H) * Real.exp (-t)) = (D * phi (i / H)) * Real.exp (-t) := by ring
      _ ≤ e.phiHi * Real.exp (-t) := mul_le_mul_of_nonneg_right h2 hexp0
      _ ≤ e.phiHi * ((96 * B ^ 4 + 48 * a ^ 2 * B ^ 2
          - (96 * a * B ^ 3 + 16 * a ^ 3 * B) + 5 * a ^ 4) / (96 * B ^ 4)) :=
        mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg _)
      _ ≤ e'.phiHi := h3

/-- The tail part of validity propagates from `i + 1` down to `i`. -/
lemma tail_step {e e' : Entry} {i : ℕ} (hv : e'.Valid (i + 1)) (hi : i + 1 ≤ H * H)
    (hok : tailStepOK e e' i = true) :
    (e.tailLo : ℝ) ≤ D * (1 - Φ (i / H)) ∧ (D : ℝ) * (1 - Φ (i / H)) ≤ e.tailHi := by
  have hH := H_pos
  have hR := R_pos
  have hD := D_pos
  have hden := slDen_pos
  simp only [tailStepOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hhi, hlo⟩ := hok
  have hhi' := (Nat.cast_le (α := ℝ)).mpr hhi
  have hlo' := (Nat.cast_le (α := ℝ)).mpr hlo
  push_cast at hhi' hlo'
  have hid : (i + 1) * R ≤ Q := by
    unfold Q; exact Nat.mul_le_mul_right R hi
  obtain ⟨hs1, hs2⟩ := slice_bounds hv hid
  have hpt : ((i + 1 : ℕ) : ℝ) / H - (R : ℝ) / (H * R) = i / H := by
    push_cast; field_simp; ring
  rw [hpt] at hs1 hs2
  obtain ⟨-, -, ht1, ht2⟩ := hv
  have hsplit : (D : ℝ) * (1 - Φ (i / H)) = D * (1 - Φ ((i + 1 : ℕ) / H))
      + D * (Φ ((i + 1 : ℕ) / H) - Φ (i / H)) := by ring
  rw [hsplit]
  constructor
  · have h3 : (e.tailLo : ℝ) ≤ e'.tailLo + (e'.phiLo : ℝ) * (slLoP (i + 1) R - slLoN R) / slDen := by
      rw [← sub_le_iff_le_add', le_div_iff₀ hden]
      nlinarith
    linarith
  · have h3 : (e'.tailHi : ℝ) + (e'.phiHi : ℝ) * slUp (i + 1) R / slDen ≤ e.tailHi := by
      rw [← le_sub_iff_add_le', div_le_iff₀ hden]
      nlinarith
    linarith

/-- **A table passing the check is correct.** -/
theorem valid_of_tableOK {tab : ℕ → Entry} {imax : ℕ} (h : tableOK tab imax = true) :
    ∀ i ≤ imax, (tab i).Valid i := by
  have hH := H_pos
  have hD := D_pos
  simp only [tableOK, baseOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨hb1, hb2⟩, hb3⟩, hb4⟩, hb5⟩, hb6⟩, hstep⟩ := h
  -- the density bounds, upwards
  have hphi : ∀ i ≤ imax, ((tab i).phiLo : ℝ) ≤ D * phi (i / H) ∧
      (D : ℝ) * phi (i / H) ≤ (tab i).phiHi := by
    intro i
    induction i with
    | zero =>
      intro _
      have hpiLo : (piLo : ℝ) / piDen < π := by
        have := Real.pi_gt_d20
        have e : (piLo : ℝ) / piDen = 3.14159265358979323846 := by norm_num [piLo, piDen]
        rw [e]; exact this
      have hpiHi : π < (piHi : ℝ) / piDen := by
        have := Real.pi_lt_d20
        have e : (piHi : ℝ) / piDen = 3.14159265358979323847 := by norm_num [piHi, piDen]
        rw [e]; exact this
      have hpd : (0 : ℝ) < piDen := by norm_num [piDen]
      have h1 := (Nat.cast_le (α := ℝ)).mpr hb1
      have h2 := (Nat.cast_le (α := ℝ)).mpr hb2
      push_cast at h1 h2
      simp only [Nat.cast_zero, zero_div]
      constructor
      · have hle : ((tab 0).phiLo / D : ℝ) ≤ phi 0 := by
          refine le_phi_zero ?_
          rw [div_pow, div_mul_eq_mul_div, div_le_one (by positivity)]
          have h3 : (π : ℝ) * piDen < piHi := by
            rw [lt_div_iff₀ hpd] at hpiHi; exact hpiHi
          have h4 : (0 : ℝ) ≤ ((tab 0).phiLo : ℝ) ^ 2 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left h3.le h4]
        rw [div_le_iff₀ hD] at hle
        linarith
      · have hle : phi 0 ≤ ((tab 0).phiHi / D : ℝ) := by
          refine phi_zero_le (by positivity) ?_
          rw [div_pow, div_mul_eq_mul_div, one_le_div (by positivity)]
          have h3 : (piLo : ℝ) < π * piDen := by
            rw [div_lt_iff₀ hpd] at hpiLo; exact hpiLo
          have h4 : (0 : ℝ) ≤ ((tab 0).phiHi : ℝ) ^ 2 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left h3.le h4]
        rw [le_div_iff₀ hD] at hle
        linarith
    | succ i ih =>
      intro hi
      have hi' : i < imax := hi
      obtain ⟨ih1, ih2⟩ := ih hi'.le
      have hbound : 2 * i + 1 ≤ 2 * H * H := by
        have h2 : i + 1 ≤ H * H := lt_of_lt_of_le hi' hb6
        have h3 : 2 * i + 1 ≤ 2 * (i + 1) := by omega
        exact h3.trans (by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left 2 h2)
      exact phi_step ih1 ih2 hbound (hstep i hi').1
  -- the tail bounds, downwards
  have htail : ∀ k ≤ imax, (tab (imax - k)).Valid (imax - k) := by
    intro k
    induction k with
    | zero =>
      intro _
      obtain ⟨hp1, hp2⟩ := hphi imax le_rfl
      refine ⟨hp1, hp2, ?_, ?_⟩
      · simp only [Nat.sub_zero, hb4, Nat.cast_zero]
        have := cdf_le_one (gaussianReal 0 1) ((imax : ℝ) / H)
        nlinarith
      · simp only [Nat.sub_zero]
        have hX : (0 : ℝ) < (imax : ℝ) / H := by
          have : (0 : ℝ) < imax := by exact_mod_cast hb5
          positivity
        have hm := one_sub_cdf_le hX
        have h3 := (Nat.cast_le (α := ℝ)).mpr hb3
        push_cast at h3
        have himax : (0 : ℝ) < imax := by exact_mod_cast hb5
        have h4 : phi ((imax : ℝ) / H) / ((imax : ℝ) / H) = phi ((imax : ℝ) / H) * H / imax := by
          field_simp
        rw [h4] at hm
        have h5 : (D : ℝ) * (phi ((imax : ℝ) / H) * H / imax) ≤ (tab imax).tailHi := by
          have : (D : ℝ) * (phi ((imax : ℝ) / H) * H / imax)
              = (D * phi ((imax : ℝ) / H)) * H / imax := by ring
          rw [this, div_le_iff₀ himax]
          nlinarith
        nlinarith
    | succ k ih =>
      intro hk
      have hk' : k < imax := hk
      have hv := ih hk'.le
      have hidx : imax - k = (imax - (k + 1)) + 1 := by omega
      rw [hidx] at hv
      have hlt : imax - (k + 1) < imax := by omega
      obtain ⟨hp1, hp2⟩ := hphi (imax - (k + 1)) hlt.le
      have hbound : imax - (k + 1) + 1 ≤ H * H := le_trans (by omega) hb6
      obtain ⟨ht1, ht2⟩ := tail_step hv hbound (hstep _ hlt).2
      exact ⟨hp1, hp2, ht1, ht2⟩
  intro i hi
  have := htail (imax - i) (Nat.sub_le _ _)
  rwa [Nat.sub_sub_self hi] at this

section Eval

variable (tab : ℕ → Entry) (imax : ℕ)

/-- Upper bound for `D (1 - Φ(y / (H R)))`, `y : ℕ`. -/
def tailUp (y : ℕ) : ℕ :=
  let i := (y + (R - 1)) / R
  if imax < i then (tab imax).tailHi
  else (tab i).tailHi + ((tab i).phiHi * slUp i (i * R - y)) / slDen + 1

/-- Lower bound for `D (1 - Φ(y / (H R)))`, `y : ℕ`. -/
def tailDown (y : ℕ) : ℕ :=
  let i := (y + (R - 1)) / R
  if imax < i then 0
  else (tab i).tailLo + ((tab i).phiLo * (slLoP i (i * R - y) - slLoN (i * R - y))) / slDen

/-- Upper bound for `D Φ(y / (H R))`, `y : ℤ`. -/
def PhiUp (y : ℤ) : ℕ :=
  if 0 ≤ y then D - tailDown tab imax y.toNat else tailUp tab imax (-y).toNat

/-- Lower bound for `D Φ(y / (H R))`, `y : ℤ`. -/
def PhiDown (y : ℤ) : ℕ :=
  if 0 ≤ y then D - tailUp tab imax y.toNat else tailDown tab imax (-y).toNat

variable {tab imax}

lemma ceil_facts (y : ℕ) :
    y ≤ (y + (R - 1)) / R * R ∧ (y + (R - 1)) / R * R - y ≤ R := by
  have hR : 0 < R := by norm_num [R]
  have h1 : (y + (R - 1)) / R * R ≤ y + (R - 1) := Nat.div_mul_le_self _ _
  have h2 : y + (R - 1) < (y + (R - 1)) / R * R + R := Nat.lt_div_mul_add hR
  generalize (y + (R - 1)) / R * R = z at h1 h2
  constructor <;> omega

lemma natCast_div_lt (a : ℕ) {b : ℕ} (hb : 0 < b) : (a : ℝ) / b < (a / b : ℕ) + 1 := by
  have h := Nat.lt_div_mul_add (a := a) hb
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have h' : (a : ℝ) < (a / b : ℕ) * b + b := by exact_mod_cast h
  rw [div_lt_iff₀ hb']
  linarith

lemma slDen_pos_nat : 0 < slDen := by norm_num [slDen, Q, H, R]

theorem tailUp_spec (hv : ∀ i ≤ imax, (tab i).Valid i) (himax : imax ≤ H * H) (y : ℕ) :
    (D : ℝ) * (1 - Φ ((y : ℝ) / (H * R))) ≤ tailUp tab imax y := by
  have hH := H_pos
  have hR := R_pos
  have hD := D_pos
  obtain ⟨hc1, hc2⟩ := ceil_facts y
  unfold tailUp
  set i := (y + (R - 1)) / R with hi
  by_cases hlt : imax < i
  · simp only [hlt, ite_true]
    have hge : (imax : ℝ) / H ≤ (y : ℝ) / (H * R) := by
      have h1 : (imax + 1) * R ≤ y + R := by
        have : (imax + 1) * R ≤ i * R := Nat.mul_le_mul_right R hlt
        have h2 : i * R ≤ y + (R - 1) := Nat.div_mul_le_self _ _
        have h3 : 0 < R := by norm_num [R]
        generalize i * R = z at this h2
        generalize (imax + 1) * R = w at this ⊢
        omega
      have h1' : ((imax : ℝ) + 1) * R ≤ y + R := by exact_mod_cast h1
      rw [div_le_div_iff₀ hH (by positivity)]
      nlinarith
    have hmono := monotone_cdf (gaussianReal 0 1) hge
    obtain ⟨-, -, -, h4⟩ := hv imax le_rfl
    nlinarith
  · simp only [hlt, ite_false]
    have hile : i ≤ imax := not_lt.mp hlt
    have hval := hv i hile
    set d := i * R - y with hd
    have hdR : d ≤ R := hc2
    have hid : i * d ≤ Q := by
      unfold Q
      exact Nat.mul_le_mul (hile.trans himax) hdR
    have hdcast : (d : ℝ) = (i : ℝ) * R - y := by
      rw [hd, Nat.cast_sub hc1]; push_cast; ring
    have hx : (y : ℝ) / (H * R) = (i : ℝ) / H - d / (H * R) := by
      rw [hdcast]; field_simp; ring
    obtain ⟨-, hs2⟩ := slice_bounds hval hid
    obtain ⟨-, -, -, h4⟩ := hval
    rw [hx]
    have hsplit : (D : ℝ) * (1 - Φ ((i : ℝ) / H - d / (H * R))) = D * (1 - Φ (i / H))
        + D * (Φ (i / H) - Φ ((i : ℝ) / H - d / (H * R))) := by ring
    rw [hsplit]
    have hfloor := natCast_div_lt ((tab i).phiHi * slUp i d) slDen_pos_nat
    push_cast at hfloor ⊢
    linarith

theorem tailDown_spec (hv : ∀ i ≤ imax, (tab i).Valid i) (himax : imax ≤ H * H) (y : ℕ) :
    (tailDown tab imax y : ℝ) ≤ D * (1 - Φ ((y : ℝ) / (H * R))) := by
  have hH := H_pos
  have hR := R_pos
  have hD := D_pos
  obtain ⟨hc1, hc2⟩ := ceil_facts y
  unfold tailDown
  set i := (y + (R - 1)) / R with hi
  by_cases hlt : imax < i
  · simp only [hlt, ite_true, Nat.cast_zero]
    have := cdf_le_one (gaussianReal 0 1) ((y : ℝ) / (H * R))
    nlinarith
  · simp only [hlt, ite_false]
    have hile : i ≤ imax := not_lt.mp hlt
    have hval := hv i hile
    set d := i * R - y with hd
    have hdR : d ≤ R := hc2
    have hid : i * d ≤ Q := by
      unfold Q
      exact Nat.mul_le_mul (hile.trans himax) hdR
    have hdcast : (d : ℝ) = (i : ℝ) * R - y := by
      rw [hd, Nat.cast_sub hc1]; push_cast; ring
    have hx : (y : ℝ) / (H * R) = (i : ℝ) / H - d / (H * R) := by
      rw [hdcast]; field_simp; ring
    obtain ⟨hs1, -⟩ := slice_bounds hval hid
    obtain ⟨-, -, h3, -⟩ := hval
    rw [hx]
    have hsplit : (D : ℝ) * (1 - Φ ((i : ℝ) / H - d / (H * R))) = D * (1 - Φ (i / H))
        + D * (Φ (i / H) - Φ ((i : ℝ) / H - d / (H * R))) := by ring
    have hmono : Φ ((i : ℝ) / H - d / (H * R)) ≤ Φ (i / H) :=
      monotone_cdf _ (by have : (0 : ℝ) ≤ (d : ℝ) / (H * R) := by positivity
                         linarith)
    rw [hsplit]
    push_cast
    by_cases hsub : slLoN d ≤ slLoP i d
    · have hfloor : (((tab i).phiLo * (slLoP i d - slLoN d) / slDen : ℕ) : ℝ)
          ≤ ((tab i).phiLo : ℝ) * (slLoP i d - slLoN d) / slDen := by
        refine Nat.cast_div_le.trans (le_of_eq ?_)
        rw [Nat.cast_mul, Nat.cast_sub hsub]
      linarith
    · have hz : slLoP i d - slLoN d = 0 := Nat.sub_eq_zero_of_le (not_le.mp hsub).le
      rw [hz]
      simp only [mul_zero, Nat.zero_div, Nat.cast_zero, add_zero]
      nlinarith

theorem PhiUp_spec (hv : ∀ i ≤ imax, (tab i).Valid i) (himax : imax ≤ H * H) (y : ℤ) :
    (D : ℝ) * Φ ((y : ℝ) / (H * R)) ≤ PhiUp tab imax y := by
  have hD := D_pos
  unfold PhiUp
  by_cases hy : 0 ≤ y
  · simp only [hy, ite_true]
    have hspec := tailDown_spec hv himax y.toNat
    have hcast : ((y.toNat : ℕ) : ℝ) = (y : ℝ) := by
      have : ((y.toNat : ℤ) : ℝ) = (y : ℝ) := by rw [Int.toNat_of_nonneg hy]
      exact_mod_cast this
    rw [hcast] at hspec
    have hle1 : Φ ((y : ℝ) / (H * R)) ≤ 1 := cdf_le_one _ _
    have h0 : 0 ≤ Φ ((y : ℝ) / (H * R)) := cdf_nonneg _ _
    have hle : tailDown tab imax y.toNat ≤ D := by
      have : (tailDown tab imax y.toNat : ℝ) ≤ D := by nlinarith
      exact_mod_cast this
    rw [Nat.cast_sub hle]
    linarith
  · simp only [hy, ite_false]
    have hy' : 0 ≤ -y := by omega
    have hspec := tailUp_spec hv himax (-y).toNat
    have hcast : (((-y).toNat : ℕ) : ℝ) = -(y : ℝ) := by
      have : (((-y).toNat : ℤ) : ℝ) = ((-y : ℤ) : ℝ) := by rw [Int.toNat_of_nonneg hy']
      rw [Int.cast_neg] at this
      exact_mod_cast this
    rw [hcast] at hspec
    have hneg : (y : ℝ) / (H * R) = -(-(y : ℝ) / (H * R)) := by ring
    rw [hneg, cdf_gaussian_neg]
    exact hspec

theorem PhiDown_spec (hv : ∀ i ≤ imax, (tab i).Valid i) (himax : imax ≤ H * H) (y : ℤ) :
    (PhiDown tab imax y : ℝ) ≤ D * Φ ((y : ℝ) / (H * R)) := by
  have hD := D_pos
  unfold PhiDown
  by_cases hy : 0 ≤ y
  · simp only [hy, ite_true]
    have hspec := tailUp_spec hv himax y.toNat
    have hcast : ((y.toNat : ℕ) : ℝ) = (y : ℝ) := by
      have : ((y.toNat : ℤ) : ℝ) = (y : ℝ) := by rw [Int.toNat_of_nonneg hy]
      exact_mod_cast this
    rw [hcast] at hspec
    have h0 : 0 ≤ Φ ((y : ℝ) / (H * R)) := cdf_nonneg _ _
    by_cases hle : tailUp tab imax y.toNat ≤ D
    · rw [Nat.cast_sub hle]
      linarith
    · rw [Nat.sub_eq_zero_of_le (not_le.mp hle).le]
      simp only [Nat.cast_zero]
      positivity
  · simp only [hy, ite_false]
    have hy' : 0 ≤ -y := by omega
    have hspec := tailDown_spec hv himax (-y).toNat
    have hcast : (((-y).toNat : ℕ) : ℝ) = -(y : ℝ) := by
      have : (((-y).toNat : ℤ) : ℝ) = ((-y : ℤ) : ℝ) := by rw [Int.toNat_of_nonneg hy']
      rw [Int.cast_neg] at this
      exact_mod_cast this
    rw [hcast] at hspec
    have hneg : (y : ℝ) / (H * R) = -(-(y : ℝ) / (H * R)) := by ring
    rw [hneg, cdf_gaussian_neg]
    exact hspec

/-- Monotone form: an upper bound for `D Φ x` from any lattice point above `x`. -/
theorem PhiUp_le (hv : ∀ i ≤ imax, (tab i).Valid i) (himax : imax ≤ H * H) {x : ℝ} {y : ℤ}
    (hxy : x ≤ (y : ℝ) / (H * R)) : (D : ℝ) * Φ x ≤ PhiUp tab imax y :=
  (mul_le_mul_of_nonneg_left (monotone_cdf _ hxy) D_pos.le).trans (PhiUp_spec hv himax y)

/-- Monotone form: a lower bound for `D Φ x` from any lattice point below `x`. -/
theorem PhiDown_le (hv : ∀ i ≤ imax, (tab i).Valid i) (himax : imax ≤ H * H) {x : ℝ} {y : ℤ}
    (hxy : (y : ℝ) / (H * R) ≤ x) : (PhiDown tab imax y : ℝ) ≤ D * Φ x :=
  (PhiDown_spec hv himax y).trans (mul_le_mul_of_nonneg_left (monotone_cdf _ hxy) D_pos.le)

end Eval

end Applied.Statistics.NormalTable
