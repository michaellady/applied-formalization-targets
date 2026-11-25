import Applied.Coding.Delsarte

/-!
# Delsarte linear programming bound: checked certificates

* `lpCheck`: a Boolean checker for an integer dual certificate of the Delsarte linear program,
  using a fast evaluation of binomial coefficients; `IsCode.card_mul_le_of_lpCheck` shows that a
  certificate accepted by the checker gives the bound of `IsCode.card_mul_le_lp`.
* `IsCode.card_le_of_length_eight_dist_four`: `A(8, 4) ≤ 16`.
* `IsCode.card_le_of_length_sixteen_dist_six`: `A(16, 6) ≤ 256`.
* `IsCode.card_le_of_length_twentyFour_dist_eight`: `A(24, 8) ≤ 4096`.

The certificates were found with an exact rational simplex method outside Lean; Lean only checks
them (with `decide`, evaluated by the kernel).
-/

open Finset

namespace Applied.Coding

/-- Binomial coefficients through descending factorials (fast to evaluate in the kernel). -/
def chooseF (n k : ℕ) : ℕ := n.descFactorial k / k.factorial

lemma chooseF_eq (n k : ℕ) : chooseF n k = n.choose k :=
  (Nat.choose_eq_descFactorial_div_factorial n k).symm

/-- `kraw` computed with `chooseF`. -/
def krawF (w m k : ℕ) : ℤ :=
  ∑ a ∈ range (k + 1), (-1) ^ a * ((chooseF w a : ℤ) * (chooseF m (k - a) : ℤ))

lemma krawF_eq (w m k : ℕ) : krawF w m k = kraw w m k := by
  rw [kraw, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [krawF, chooseF_eq]

/-- Checks the dual feasibility conditions `D + ∑_{k=1}^{n} γ_k K_k(i) ≤ 0` for `d ≤ i ≤ n`,
where `γ_k = γ.getD k 0`. -/
def lpCheck (n d D : ℕ) (γ : List ℕ) : Bool :=
  (List.range (n + 1)).all fun i =>
    decide (i < d) || decide ((D : ℤ) + ∑ k ∈ Icc 1 n, (γ.getD k 0 : ℤ) * krawF i (n - i) k ≤ 0)

/-- A certificate accepted by `lpCheck` gives the Delsarte bound
`|C| · D ≤ D + ∑_{k=1}^{n} γ_k C(n, k)`. -/
theorem IsCode.card_mul_le_of_lpCheck {n d D : ℕ} {γ : List ℕ} {C : Finset (BWord n)}
    (hC : IsCode d C) (h : lpCheck n d D γ = true) :
    C.card * D ≤ D + ∑ k ∈ Icc 1 n, γ.getD k 0 * chooseF n k := by
  simp only [chooseF_eq]
  refine hC.card_mul_le_lp D (fun k => γ.getD k 0) fun i hdi hin => ?_
  rw [lpCheck, List.all_eq_true] at h
  have hi := h i (List.mem_range.mpr (by omega))
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hi
  rcases hi with hi | hi
  · omega
  · simpa [krawF_eq] using hi

/-- **`A(8, 4) ≤ 16`** (Delsarte LP bound; attained by the extended Hamming code, which is not
formalized here). -/
theorem IsCode.card_le_of_length_eight_dist_four {C : Finset (BWord 8)} (hC : IsCode 4 C) :
    C.card ≤ 16 := by
  have h := hC.card_mul_le_of_lpCheck (D := 4) (γ := [0, 4, 1]) (by decide)
  have h2 : 4 + ∑ k ∈ Icc 1 8, [0, 4, 1].getD k 0 * chooseF 8 k = 16 * 4 := by decide
  omega

/-- **`A(16, 6) ≤ 256`** (Delsarte LP bound; attained by the Nordstrom–Robinson code, which is
not formalized here). -/
theorem IsCode.card_le_of_length_sixteen_dist_six {C : Finset (BWord 16)} (hC : IsCode 6 C) :
    C.card ≤ 256 := by
  have h := hC.card_mul_le_of_lpCheck (D := 24080)
    (γ := [0, 17325, 7224, 3592, 954, 90, 0, 0, 0, 35, 0, 0, 250]) (by decide)
  have h2 : 24080 + ∑ k ∈ Icc 1 16,
      [0, 17325, 7224, 3592, 954, 90, 0, 0, 0, 35, 0, 0, 250].getD k 0 * chooseF 16 k
      = 256 * 24080 := by decide
  omega

/-- **`A(24, 8) ≤ 4096`** (Delsarte LP bound; attained by the extended Golay code, which is not
formalized here). -/
theorem IsCode.card_le_of_length_twentyFour_dist_eight {C : Finset (BWord 24)}
    (hC : IsCode 8 C) : C.card ≤ 4096 := by
  have h := hC.card_mul_le_of_lpCheck (D := 70803936)
    (γ := [0, 70803936, 39894981, 17491992, 5865620, 1516624, 209571, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 141639, 824776, 2188796, 4142544, 3865785]) (by decide)
  have h2 : 70803936 + ∑ k ∈ Icc 1 24,
      [0, 70803936, 39894981, 17491992, 5865620, 1516624, 209571, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 141639, 824776, 2188796, 4142544, 3865785].getD k 0 * chooseF 24 k
      = 4096 * 70803936 := by decide
  omega

end Applied.Coding
