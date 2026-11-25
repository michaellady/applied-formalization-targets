import Applied.InformationTheory.ShannonCapacity

/-!
# Lower bounds for the Shannon capacity of the 7-cycle from explicit independent sets

Words of length `d` over `ℤ/7` are encoded as natural numbers `< 7ᵈ` in base 7 (digit `i` is
coordinate `i`). A Boolean checker `pairsSep d L` tests that any two entries of the list `L`
differ by `2, 3, 4` or `5` modulo 7 in some coordinate, i.e. are distinct and non-adjacent in the
strong power `C₇^{⊠d}`. It is proved correct once (`indepNum_ge_of_pairsSep`), and evaluated by
`decide` (in the kernel) on explicit lists found by a computer search (tabu search; the lists
themselves are certificates and need not be trusted).

* `ten_le_indepNum_strongPow_two`: `10 ≤ α(C₇^{⊠2})`;
* `thirtyThree_le_indepNum_strongPow_three`: `33 ≤ α(C₇^{⊠3})`;
* `oneHundredEight_le_indepNum_strongPow_four`: `108 ≤ α(C₇^{⊠4})`;
* the corresponding bounds `√10 ≤ Θ(C₇)`, `33^{1/3} ≤ Θ(C₇)`, `108^{1/4} ≤ Θ(C₇)`
  (`108^{1/4} ≈ 3.2237`).
-/

open Finset

namespace Applied.InformationTheory

namespace C7Search

/-- Two letters of `ℤ/7` (given as naturals) are *far*: they differ by `2, 3, 4` or `5` mod 7. -/
def far (a b : ℕ) : Bool := decide (2 ≤ (a + 7 - b) % 7 ∧ (a + 7 - b) % 7 ≤ 5)

/-- Digit `i` of `c` in base 7. -/
def digit (c i : ℕ) : ℕ := c / 7 ^ i % 7

/-- Two encoded words of length `d` are far in some coordinate. -/
def sep (d a b : ℕ) : Bool := (List.range d).any fun i => far (digit a i) (digit b i)

/-- Every two entries of the list (at different positions) are separated. -/
def pairsSep (d : ℕ) : List ℕ → Bool
  | [] => true
  | a :: t => t.all (sep d a) && pairsSep d t

/-- Decoding a natural number into a word of length `d` over `Fin 7`. -/
def decode (d c : ℕ) : Fin d → Fin 7 := fun i => ⟨digit c i, Nat.mod_lt _ (by norm_num)⟩

lemma far_spec : ∀ x y : Fin 7, far x.val y.val = true →
    x ≠ y ∧ ¬(SimpleGraph.cycleGraph 7).Adj x y := by
  intro x y
  rw [SimpleGraph.cycleGraph_adj]
  revert x y
  decide

lemma pairwise_of_pairsSep {d : ℕ} : ∀ {L : List ℕ}, pairsSep d L = true →
    L.Pairwise fun a b => sep d a b = true
  | [], _ => List.Pairwise.nil
  | a :: t, h => by
    simp only [pairsSep, Bool.and_eq_true, List.all_eq_true] at h
    exact List.Pairwise.cons h.1 (pairwise_of_pairsSep h.2)

lemma sep_spec {d a b : ℕ} (h : sep d a b = true) :
    ∃ i : Fin d, decode d a i ≠ decode d b i ∧
      ¬(SimpleGraph.cycleGraph 7).Adj (decode d a i) (decode d b i) := by
  simp only [sep, List.any_eq_true, List.mem_range] at h
  obtain ⟨i, hi, hf⟩ := h
  exact ⟨⟨i, hi⟩, far_spec (decode d a ⟨i, hi⟩) (decode d b ⟨i, hi⟩) hf⟩

lemma sep_symm {d a b : ℕ} (h : sep d a b = true) : sep d b a = true := by
  simp only [sep, List.any_eq_true, List.mem_range] at h ⊢
  obtain ⟨i, hi, hf⟩ := h
  refine ⟨i, hi, ?_⟩
  have : ∀ x y : Fin 7, far x.val y.val = true → far y.val x.val = true := by decide
  exact this ⟨digit a i, Nat.mod_lt _ (by norm_num)⟩ ⟨digit b i, Nat.mod_lt _ (by norm_num)⟩ hf

lemma sep_of_mem {d : ℕ} : ∀ {L : List ℕ}, L.Pairwise (fun a b => sep d a b = true) →
    ∀ a ∈ L, ∀ b ∈ L, a ≠ b → sep d a b = true
  | [], _ => by simp
  | x :: t, h => by
    intro a ha b hb hab
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp ha with ha1 | ha1 <;> rcases List.mem_cons.mp hb with hb1 | hb1
    · exact absurd (ha1.trans hb1.symm) hab
    · rw [ha1]; exact h.1 b hb1
    · rw [hb1]; exact sep_symm (h.1 a ha1)
    · exact sep_of_mem h.2 a ha1 b hb1 hab

/-- **Correctness of the checker.** If `pairsSep d L` holds, then `α(C₇^{⊠d}) ≥ |L|`. -/
theorem indepNum_ge_of_pairsSep {d : ℕ} {L : List ℕ} (h : pairsSep d L = true) :
    L.length ≤ (strongPow (SimpleGraph.cycleGraph 7) d).indepNum := by
  classical
  have hp := pairwise_of_pairsSep h
  -- separated codes give different words
  have hne : ∀ {a b : ℕ}, sep d a b = true → decode d a ≠ decode d b := by
    intro a b hab heq
    obtain ⟨i, hi, -⟩ := sep_spec hab
    exact hi (congrFun heq i)
  have hnodup : (L.map (decode d)).Nodup :=
    List.Pairwise.map _ (fun a b hab => hne hab) hp
  set s : Finset (Fin d → Fin 7) := (L.map (decode d)).toFinset with hs
  have hcard : s.card = L.length := by
    rw [hs, List.toFinset_card_of_nodup hnodup, List.length_map]
  have hsep := sep_of_mem hp
  have hind : (strongPow (SimpleGraph.cycleGraph 7) d).IsIndepSet (s : Set (Fin d → Fin 7)) := by
    intro f hf g hg hfg hadj
    rw [hs, Finset.mem_coe, List.mem_toFinset, List.mem_map] at hf hg
    obtain ⟨a, ha, rfl⟩ := hf
    obtain ⟨b, hb, rfl⟩ := hg
    have hab : a ≠ b := fun h' => hfg (by rw [h'])
    obtain ⟨i, h1, h2⟩ := sep_spec (hsep a ha b hb hab)
    rcases hadj.2 i with h | h
    · exact h1 h
    · exact h2 h
  have := hind.card_le_indepNum
  rwa [hcard] at this

end C7Search

open C7Search

/-- Ten pairwise non-confusable words of length 2 (found by computer search). -/
def c7Words2 : List ℕ :=
  [5, 8, 10, 20, 22, 24, 34, 37, 39, 42]

/-- 33 pairwise non-confusable words of length 3 (found by computer search). -/
def c7Words3 : List ℕ :=
  [
    6, 9, 14, 23, 67, 81, 83, 92, 94, 103, 113, 118, 127, 147, 149, 164, 178, 188, 208, 218,
    223, 232, 242, 252, 254, 269, 293, 298, 313, 322, 327, 332, 337]

/-- 108 pairwise non-confusable words of length 4 (found by computer search). -/
def c7Words4 : List ℕ :=
  [
    8, 45, 92, 97, 118, 126, 131, 153, 165, 200, 236, 270, 283, 305, 317, 371, 376, 410, 423,
    445, 457, 492, 528, 562, 575, 597, 609, 650, 680, 685, 695, 732, 749, 779, 813, 818, 826,
    847, 852, 882, 887, 923, 957, 970, 991, 1004, 1058, 1063, 1071, 1097, 1110, 1132, 1144,
    1179, 1215, 1249, 1262, 1283, 1296, 1330, 1367, 1377, 1389, 1424, 1436, 1470, 1507, 1541,
    1546, 1554, 1575, 1580, 1651, 1659, 1664, 1685, 1698, 1716, 1752, 1791, 1799, 1804, 1825,
    1838, 1872, 1909, 1943, 1956, 1977, 1990, 2012, 2024, 2071, 2083, 2117, 2130, 2164, 2201,
    2235, 2248, 2269, 2274, 2282, 2304, 2309, 2379, 2387, 2392]

/-- `10 ≤ α(C₇ ⊠ C₇)`. -/
theorem ten_le_indepNum_strongPow_two :
    10 ≤ (strongPow (SimpleGraph.cycleGraph 7) 2).indepNum :=
  indepNum_ge_of_pairsSep (L := c7Words2) (by decide)

/-- `33 ≤ α(C₇^{⊠3})`. -/
theorem thirtyThree_le_indepNum_strongPow_three :
    33 ≤ (strongPow (SimpleGraph.cycleGraph 7) 3).indepNum :=
  indepNum_ge_of_pairsSep (L := c7Words3) (by decide)

/-- `108 ≤ α(C₇^{⊠4})`. -/
theorem oneHundredEight_le_indepNum_strongPow_four :
    108 ≤ (strongPow (SimpleGraph.cycleGraph 7) 4).indepNum :=
  indepNum_ge_of_pairsSep (L := c7Words4) (by decide)

/-- From `m ≤ α(G^{⊠(k+1)})` to `m^{1/(k+1)} ≤ Θ(G)`. -/
theorem rpow_le_shannonCapacity_of_le {V : Type*} [Fintype V] (G : SimpleGraph V) (k m : ℕ)
    (h : m ≤ (strongPow G (k + 1)).indepNum) :
    (m : ℝ) ^ (((k + 1 : ℕ) : ℝ)⁻¹) ≤ shannonCapacity G :=
  le_trans (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast h) (by positivity))
    (le_shannonCapacity G k)

/-- `√10 ≤ Θ(C₇)`. -/
theorem sqrt_ten_le_shannonCapacity_cycleGraph_seven :
    Real.sqrt 10 ≤ shannonCapacity (SimpleGraph.cycleGraph 7) := by
  have h := rpow_le_shannonCapacity_of_le _ 1 10 ten_le_indepNum_strongPow_two
  rw [Real.sqrt_eq_rpow]
  convert h using 2; norm_num

/-- `33^{1/3} ≤ Θ(C₇)` (the value of Baumert et al., 1971). -/
theorem cbrt_thirtyThree_le_shannonCapacity_cycleGraph_seven :
    (33 : ℝ) ^ ((1 : ℝ) / 3) ≤ shannonCapacity (SimpleGraph.cycleGraph 7) := by
  have h := rpow_le_shannonCapacity_of_le _ 2 33 thirtyThree_le_indepNum_strongPow_three
  convert h using 2; norm_num

/-- `108^{1/4} ≤ Θ(C₇)` (`≈ 3.2237`). -/
theorem rpow_oneHundredEight_le_shannonCapacity_cycleGraph_seven :
    (108 : ℝ) ^ ((1 : ℝ) / 4) ≤ shannonCapacity (SimpleGraph.cycleGraph 7) := by
  have h := rpow_le_shannonCapacity_of_le _ 3 108 oneHundredEight_le_indepNum_strongPow_four
  convert h using 2; norm_num

/-- `3.2 < 108^{1/4}`, so `3.2 < Θ(C₇)`. -/
theorem three_point_two_lt_shannonCapacity_cycleGraph_seven :
    (16 / 5 : ℝ) < shannonCapacity (SimpleGraph.cycleGraph 7) := by
  refine lt_of_lt_of_le ?_ rpow_oneHundredEight_le_shannonCapacity_cycleGraph_seven
  have h : ((16 / 5 : ℝ) ^ (4 : ℝ)) ^ ((1 : ℝ) / 4) = 16 / 5 := by
    rw [← Real.rpow_mul (by norm_num)]; norm_num
  rw [← h]
  refine Real.rpow_lt_rpow (by positivity) ?_ (by norm_num)
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

end Applied.InformationTheory
