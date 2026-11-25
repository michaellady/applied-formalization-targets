import Applied.Coding.Varshamov

/-!
# The Delsarte linear programming bound for binary codes

* `kraw w m k = ∑_{a + b = k} (-1)ᵃ C(w, a) C(m, b)`: the binary Krawtchouk polynomial
  `K_k(w)` for length `n = w + m`.
* `charSum_eq_kraw`: the **Krawtchouk identity**
  `∑_{u ∈ 𝔽₂ⁿ, wt u = k} (-1)^{⟨u, z⟩} = K_k(wt z)`.
* `IsCode.sum_kraw_nonneg`: the **Delsarte inequalities**: for every code `C` and every `k`,
  `∑_{x, y ∈ C} K_k(d(x, y)) ≥ 0`.
* `IsCode.card_mul_le_lp`: the **Delsarte linear programming bound** with an integer dual
  certificate: if `D > 0`, `γ_k ≥ 0` and `D + ∑_{k=1}^{n} γ_k K_k(i) ≤ 0` for `d ≤ i ≤ n`, then
  every code of minimum distance at least `d` has `|C| · D ≤ D + ∑_{k=1}^{n} γ_k C(n, k)`.
-/

open Finset

namespace Applied.Coding

/-! ### Krawtchouk polynomials -/

/-- The binary Krawtchouk number `K_k(w) = ∑_{a + b = k} (-1)ᵃ C(w, a) C(m, b)` for words of
weight `w` and length `w + m`. -/
def kraw (w m k : ℕ) : ℤ :=
  ∑ p ∈ antidiagonal k, (-1) ^ p.1 * ((w.choose p.1 : ℤ) * (m.choose p.2 : ℤ))

lemma kraw_zero_right (w m : ℕ) : kraw w m 0 = 1 := by
  simp [kraw]

lemma kraw_zero_left (m k : ℕ) : kraw 0 m k = m.choose k := by
  rw [kraw, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro a _ ha
    simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero ha)]
  · intro h; simp at h

lemma kraw_succ_right (w m k : ℕ) : kraw w (m + 1) (k + 1) = kraw w m (k + 1) + kraw w m k := by
  simp only [kraw]
  rw [Finset.Nat.sum_antidiagonal_succ', Finset.Nat.sum_antidiagonal_succ' (n := k)]
  simp only [Nat.choose_succ_succ', Nat.choose_zero_right, Nat.cast_add, Nat.cast_one]
  simp only [mul_add, Finset.sum_add_distrib]
  ring

lemma kraw_succ_left (w m k : ℕ) : kraw (w + 1) m (k + 1) = kraw w m (k + 1) - kraw w m k := by
  simp only [kraw]
  rw [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ (n := k)]
  simp only [Nat.choose_succ_succ', Nat.choose_zero_right, Nat.cast_add, Nat.cast_one]
  simp only [add_mul, mul_add, Finset.sum_add_distrib, pow_succ, mul_neg, mul_one, neg_mul,
    Finset.sum_neg_distrib]
  ring

/-! ### Characters of `𝔽₂ⁿ` -/

/-- `χ(a) = (-1)ᵃ` for `a ∈ 𝔽₂`. -/
def chi (a : ZMod 2) : ℤ := if a = 0 then 1 else -1

lemma chi_add (a b : ZMod 2) : chi (a + b) = chi a * chi b := by
  revert a b; decide

lemma chi_zero : chi 0 = 1 := rfl

lemma chi_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    chi (∑ i ∈ s, f i) = ∏ i ∈ s, chi (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [chi_zero]
  | insert a s ha ih => rw [sum_insert ha, prod_insert ha, chi_add, ih]

/-- The inner product `⟨u, z⟩ = ∑ uᵢ zᵢ ∈ 𝔽₂`. -/
def dotp {n : ℕ} (u z : BWord n) : ZMod 2 := ∑ i, u i * z i

lemma dotp_add {n : ℕ} (u x y : BWord n) : dotp u (x + y) = dotp u x + dotp u y := by
  simp only [dotp, Pi.add_apply, mul_add, sum_add_distrib]

/-- `S(n, k, z) = ∑_{wt u = k} (-1)^{⟨u, z⟩}`. -/
def charSum (n k : ℕ) (z : BWord n) : ℤ :=
  ∑ u : BWord n, if hammingNorm u = k then chi (dotp u z) else 0

private lemma sum_zmod2 (f : ZMod 2 → ℤ) : ∑ a, f a = f 0 + f 1 := Fin.sum_univ_two f

private lemma charSum_succ_aux (n k : ℕ) (z : BWord (n + 1)) :
    charSum (n + 1) k z = charSum n k (Fin.tail z)
      + ∑ u : BWord n, if 1 + hammingNorm u = k then chi (z 0) * chi (dotp u (Fin.tail z))
        else 0 := by
  rw [charSum, ← (Fin.consEquiv fun _ : Fin (n + 1) => ZMod 2).sum_comp,
    Fintype.sum_prod_type, sum_zmod2]
  congr 1
  · refine Finset.sum_congr rfl fun u _ => ?_
    have h1 : hammingNorm (Fin.cons 0 u : BWord (n + 1)) = hammingNorm u := by
      rw [hammingNorm_succ, Fin.cons_zero, Fin.tail_cons]; simp
    have h2 : dotp (Fin.cons 0 u : BWord (n + 1)) z = dotp u (Fin.tail z) := by
      rw [dotp, Fin.sum_univ_succ, Fin.cons_zero, zero_mul, zero_add]; rfl
    show (if hammingNorm (Fin.cons 0 u : BWord (n + 1)) = k then
      chi (dotp (Fin.cons 0 u : BWord (n + 1)) z) else 0) = _
    rw [h1, h2]
  · refine Finset.sum_congr rfl fun u _ => ?_
    have h1 : hammingNorm (Fin.cons 1 u : BWord (n + 1)) = 1 + hammingNorm u := by
      rw [hammingNorm_succ, Fin.cons_zero, Fin.tail_cons]; rfl
    have h2 : chi (dotp (Fin.cons 1 u : BWord (n + 1)) z) = chi (z 0) * chi (dotp u (Fin.tail z)) := by
      rw [dotp, Fin.sum_univ_succ, Fin.cons_zero, one_mul, chi_add]; rfl
    show (if hammingNorm (Fin.cons 1 u : BWord (n + 1)) = k then
      chi (dotp (Fin.cons 1 u : BWord (n + 1)) z) else 0) = _
    rw [h1, h2]

lemma charSum_succ_zero (n : ℕ) (z : BWord (n + 1)) :
    charSum (n + 1) 0 z = charSum n 0 (Fin.tail z) := by
  rw [charSum_succ_aux]
  simp

lemma charSum_succ_succ (n k : ℕ) (z : BWord (n + 1)) :
    charSum (n + 1) (k + 1) z = charSum n (k + 1) (Fin.tail z) + chi (z 0) * charSum n k (Fin.tail z) := by
  rw [charSum_succ_aux]
  simp only [charSum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases h : hammingNorm u = k
  · simp [h, Nat.add_comm 1 k]
  · simp [h, show ¬ 1 + hammingNorm u = k + 1 by omega]

/-- **Krawtchouk identity.** `∑_{u : wt u = k} (-1)^{⟨u, z⟩} = K_k(wt z)` where the Krawtchouk
number is taken for length `n = wt z + (n - wt z)`. -/
theorem charSum_eq_kraw (n k : ℕ) (z : BWord n) :
    charSum n k z = kraw (hammingNorm z) (n - hammingNorm z) k := by
  induction n generalizing k with
  | zero =>
    have hz : z = 0 := Subsingleton.elim _ _
    subst hz
    rw [hammingNorm_zero, kraw_zero_left]
    simp only [charSum, Fintype.sum_subsingleton _ (0 : BWord 0), hammingNorm_zero, Nat.sub_zero]
    rcases k with _ | k <;> simp [dotp, chi]
  | succ n ih =>
    have hw := hammingNorm_succ z
    have hle : hammingNorm (Fin.tail z) ≤ n := by
      have := hammingNorm_le_card_fintype (x := Fin.tail z)
      simpa using this
    rcases k with _ | k
    · rw [charSum_succ_zero, ih, kraw_zero_right, kraw_zero_right]
    · rw [charSum_succ_succ, ih, ih]
      by_cases h0 : z 0 = 0
      · simp only [h0, ite_true, zero_add] at hw
        rw [h0, chi_zero, one_mul, hw, show n + 1 - hammingNorm (Fin.tail z)
          = (n - hammingNorm (Fin.tail z)) + 1 by omega, kraw_succ_right]
      · simp only [h0, ite_false] at hw
        have h1 : chi (z 0) = -1 := by simp [chi, h0]
        rw [h1, hw, show n + 1 - (1 + hammingNorm (Fin.tail z))
          = n - hammingNorm (Fin.tail z) by omega, add_comm 1, kraw_succ_left]
        ring

/-! ### Delsarte inequalities and the LP bound -/

lemma hammingDist_eq_norm_add {n : ℕ} (x y : BWord n) : hammingDist x y = hammingNorm (x + y) := by
  rw [hammingDist_eq_hammingNorm, neg_bword]

/-- **Delsarte inequalities.** For every binary code `C` of length `n` and every `k`,
`∑_{x, y ∈ C} K_k(d(x, y)) ≥ 0`. -/
theorem sum_kraw_nonneg {n : ℕ} (C : Finset (BWord n)) (k : ℕ) :
    0 ≤ ∑ x ∈ C, ∑ y ∈ C, kraw (hammingDist x y) (n - hammingDist x y) k := by
  have h : ∀ x y : BWord n, kraw (hammingDist x y) (n - hammingDist x y) k
      = ∑ u : BWord n, if hammingNorm u = k then chi (dotp u x) * chi (dotp u y) else 0 := by
    intro x y
    rw [hammingDist_eq_norm_add, ← charSum_eq_kraw, charSum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [dotp_add, chi_add]
  simp_rw [h]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := C) (t := (univ : Finset (BWord n)))]
  refine Finset.sum_nonneg fun u _ => ?_
  by_cases hu : hammingNorm u = k
  · simp only [hu, ite_true]
    rw [Finset.sum_comm, ← Finset.sum_mul_sum]
    exact mul_self_nonneg _
  · simp [hu]

/-- **Delsarte linear programming bound**, integer certificate form. Let `C` be a binary code of
length `n` and minimum distance at least `d`. Let `D > 0` and `γ : ℕ → ℕ` be such that
`D + ∑_{k=1}^{n} γ_k K_k(i) ≤ 0` for every `d ≤ i ≤ n`, where `K_k(i) = kraw i (n - i) k`. Then
`|C| · D ≤ D + ∑_{k=1}^{n} γ_k C(n, k)`. -/
theorem IsCode.card_mul_le_lp {n d : ℕ} {C : Finset (BWord n)} (hC : IsCode d C) (D : ℕ)
    (γ : ℕ → ℕ)
    (hf : ∀ i, d ≤ i → i ≤ n → (D : ℤ) + ∑ k ∈ Icc 1 n, (γ k : ℤ) * kraw i (n - i) k ≤ 0) :
    C.card * D ≤ D + ∑ k ∈ Icc 1 n, γ k * n.choose k := by
  set F : ℕ → ℤ := fun i => (D : ℤ) + ∑ k ∈ Icc 1 n, (γ k : ℤ) * kraw i (n - i) k with hF
  have hF0 : F 0 = ((D + ∑ k ∈ Icc 1 n, γ k * n.choose k : ℕ) : ℤ) := by
    simp only [hF, Nat.sub_zero, kraw_zero_left]; push_cast; rfl
  -- lower bound: `∑_{x,y} F(d(x,y)) ≥ D |C|²`
  have hlow : (D : ℤ) * (C.card * C.card) ≤ ∑ x ∈ C, ∑ y ∈ C, F (hammingDist x y) := by
    simp only [hF, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    have : 0 ≤ ∑ x ∈ C, ∑ y ∈ C, ∑ k ∈ Icc 1 n,
        (γ k : ℤ) * kraw (hammingDist x y) (n - hammingDist x y) k := by
      calc (0 : ℤ) ≤ ∑ k ∈ Icc 1 n, (γ k : ℤ) * ∑ x ∈ C, ∑ y ∈ C,
            kraw (hammingDist x y) (n - hammingDist x y) k :=
            Finset.sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg _) (sum_kraw_nonneg C k)
        _ = _ := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
    nlinarith
  -- upper bound: off-diagonal terms are `≤ 0`
  have hup : ∑ x ∈ C, ∑ y ∈ C, F (hammingDist x y) ≤ C.card * F 0 := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun x hx => ?_
    rw [← Finset.add_sum_erase C _ hx, hammingDist_self]
    have : ∑ y ∈ C.erase x, F (hammingDist x y) ≤ 0 := by
      refine Finset.sum_nonpos fun y hy => ?_
      have hxy := hC x hx y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy).symm
      exact hf _ hxy (hammingDist_le_card_fintype.trans (by simp))
    linarith
  rcases Nat.eq_zero_or_pos C.card with h0 | hpos
  · rw [h0]; simp
  have hposZ : (0 : ℤ) < C.card := by exact_mod_cast hpos
  have h : (C.card : ℤ) * (C.card * D) ≤ C.card * F 0 := by nlinarith
  have h' := le_of_mul_le_mul_left h hposZ
  rw [hF0] at h'
  exact_mod_cast h'

end Applied.Coding
