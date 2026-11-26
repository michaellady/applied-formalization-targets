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
* `threeHundredSixtySeven_le_indepNum_strongPow_five`: `367 ≤ α(C₇^{⊠5})`;
* the corresponding bounds `√10 ≤ Θ(C₇)`, `33^{1/3} ≤ Θ(C₇)`, `108^{1/4} ≤ Θ(C₇)`,
  `367^{1/5} ≤ Θ(C₇)` (`367^{1/5} > 3.2578`), and `13/4 < Θ(C₇)`.
-/

open Finset

namespace Applied.InformationTheory

namespace C7Search

/-- Two letters of `ℤ/7` (given as naturals `a, b < 7`; for larger `b` the truncated
subtraction makes this meaningless) are *far*: they differ by `2, 3, 4` or `5` mod 7. -/
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

/-- 367 pairwise non-confusable words of length 5 (found by computer search: tabu search in
`C₇^{⊠5}` started from 361 words obtained, after deleting conflicts, by reducing the
Polak–Schrijver independent set `{t (1, 7, 7², 7³, 7⁴) : t ∈ ℤ/382}` of the strong power of the
circular graph `C_{108,382}` coordinatewise via `x ↦ ⌊(7x + 65)/382⌋`). -/
def c7Words5 : List ℕ :=
  [
    0, 67, 141, 159, 219, 232, 251, 318, 383, 395, 475, 535, 560, 627, 646, 659, 711, 736,
    803, 863, 895, 955, 987, 1039, 1119, 1131, 1204, 1272, 1283, 1296, 1370, 1380, 1447, 1507,
    1539, 1599, 1624, 1698, 1757, 1775, 1848, 1867, 1927, 1940, 2008, 2026, 2060, 2073, 2091,
    2183, 2201, 2317, 2342, 2436, 2455, 2515, 2528, 2596, 2607, 2687, 2706, 2771, 2831, 2856,
    2923, 2948, 3015, 3082, 3099, 3159, 3172, 3191, 3251, 3325, 3343, 3423, 3475, 3500, 3567,
    3579, 3592, 3659, 3720, 3758, 3803, 3835, 3895, 3920, 3987, 4061, 4086, 4144, 4212, 4223,
    4236, 4303, 4315, 4395, 4414, 4479, 4496, 4588, 4613, 4680, 4705, 4811, 4824, 4891, 4903,
    4983, 5044, 5068, 5142, 5152, 5219, 5244, 5311, 5371, 5385, 5403, 5470, 5535, 5547, 5627,
    5639, 5712, 5780, 5798, 5811, 5863, 5888, 5955, 6015, 6047, 6107, 6139, 6191, 6265, 6283,
    6356, 6375, 6435, 6448, 6474, 6519, 6532, 6599, 6660, 6691, 6751, 6776, 6850, 6884, 6909,
    6976, 7050, 7068, 7128, 7141, 7247, 7279, 7339, 7364, 7431, 7456, 7530, 7588, 7607, 7667,
    7680, 7699, 7759, 7833, 7858, 7923, 7983, 8008, 8075, 8100, 8167, 8186, 8251, 8311, 8343,
    8403, 8428, 8495, 8527, 8579, 8652, 8720, 8731, 8744, 8811, 8823, 8910, 8955, 8987, 9047,
    9072, 9139, 9164, 9238, 9272, 9345, 9364, 9424, 9437, 9505, 9516, 9603, 9635, 9660, 9727,
    9752, 9819, 9879, 9893, 9918, 9963, 9976, 10043, 10055, 10135, 10147, 10220, 10246, 10304,
    10371, 10396, 10463, 10488, 10523, 10555, 10622, 10639, 10699, 10773, 10791, 10864, 10883,
    10950, 10963, 11015, 11027, 11040, 11107, 11168, 11199, 11259, 11291, 11343, 11368, 11435,
    11509, 11527, 11587, 11626, 11708, 11720, 11733, 11800, 11812, 11892, 11953, 11984, 12023,
    12096, 12115, 12175, 12188, 12207, 12267, 12341, 12351, 12431, 12516, 12583, 12608, 12682,
    12692, 12759, 12819, 12833, 12851, 12911, 12936, 13010, 13075, 13087, 13160, 13228, 13252,
    13319, 13338, 13403, 13463, 13495, 13555, 13580, 13582, 13647, 13679, 13731, 13804, 13823,
    13896, 13964, 14057, 14062, 14096, 14156, 14188, 14248, 14273, 14340, 14365, 14426, 14484,
    14486, 14511, 14578, 14603, 14670, 14737, 14754, 14814, 14894, 14906, 14986, 14998, 15128,
    15130, 15155, 15222, 15247, 15314, 15374, 15413, 15458, 15490, 15550, 15624, 15642, 15715,
    15741, 15799, 15866, 15878, 15891, 15958, 16019, 16050, 16117, 16134, 16194, 16219, 16286,
    16360, 16378, 16445, 16510, 16571, 16602, 16663, 16694, 16786]

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

set_option maxRecDepth 100000 in
/-- `367 ≤ α(C₇^{⊠5})` (the value of Polak–Schrijver, 2019). -/
theorem threeHundredSixtySeven_le_indepNum_strongPow_five :
    367 ≤ (strongPow (SimpleGraph.cycleGraph 7) 5).indepNum :=
  indepNum_ge_of_pairsSep (L := c7Words5) (by decide)

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

/-- `367^{1/5} ≤ Θ(C₇)` (`> 3.2578`; Polak–Schrijver 2019). -/
theorem rpow_threeHundredSixtySeven_le_shannonCapacity_cycleGraph_seven :
    (367 : ℝ) ^ ((1 : ℝ) / 5) ≤ shannonCapacity (SimpleGraph.cycleGraph 7) := by
  have h := rpow_le_shannonCapacity_of_le _ 4 367
    threeHundredSixtySeven_le_indepNum_strongPow_five
  convert h using 2; norm_num

/-- `3.25 < 367^{1/5}`, so `13/4 < Θ(C₇)`. -/
theorem thirteen_fourths_lt_shannonCapacity_cycleGraph_seven :
    (13 / 4 : ℝ) < shannonCapacity (SimpleGraph.cycleGraph 7) := by
  refine lt_of_lt_of_le ?_ rpow_threeHundredSixtySeven_le_shannonCapacity_cycleGraph_seven
  have h : ((13 / 4 : ℝ) ^ (5 : ℝ)) ^ ((1 : ℝ) / 5) = 13 / 4 := by
    rw [← Real.rpow_mul (by norm_num)]; norm_num
  rw [← h]
  refine Real.rpow_lt_rpow (by positivity) ?_ (by norm_num)
  rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

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
