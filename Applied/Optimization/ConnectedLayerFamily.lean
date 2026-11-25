import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Connected layer families: a quasi-polynomial length bound

The combinatorial abstraction of polytope graphs of Eisenbrand, Hähnle, Razborov and Rothvoß
("Diameter of polyhedra: limits of abstraction", Math. Oper. Res. 35 (2010)).

* `IsConnectedLayerFamily d U F t`: the layers `F 0, …, F (t - 1)` are nonempty, pairwise
  disjoint families of `d`-element subsets of the finite ground set `U`, and for `i < j < k < t`,
  `S ∈ F i` and `T ∈ F k` there is `R ∈ F j` with `S ∩ T ⊆ R`.
* `IsConnectedLayerFamily.length_le_two_mul_add`: the Kalai–Kleitman style recursion. If every
  family of the same `d` on at most `m` elements has length at most `g`, and every family of
  sets of size `d - 1` on at most `n - 1` elements has length at most `h`, then every family on
  at most `n ≤ 2 m + 1` elements has length at most `2 g + h`.
* `IsConnectedLayerFamily.length_le`: for `d ≥ 1` and `U.card ≤ n`,
  `t ≤ n * (d + 1) ^ Nat.log 2 n`.
* `IsConnectedLayerFamily.length_le_rpow`: the same as a real power,
  `t ≤ n ^ (1 + log₂ (d + 1))`.
* `IsConnectedLayerFamily.length_le_one_of_card_zero` (`d = 0`: `t ≤ 1`) and
  `IsConnectedLayerFamily.length_eq_zero_of_card_eq_zero` (`U = ∅`, `d ≥ 1`: `t = 0`).
* `isConnectedLayerFamily_window`: the sliding windows `{i, …, i + d - 1}`, `i ≤ n - d`, form a
  family of length `n - d + 1` (for `1 ≤ d ≤ n`): the hypotheses are satisfiable.
-/

namespace Applied.Optimization

variable {α : Type*} [DecidableEq α]

/-- A connected layer family of length `t`: `F 0, …, F (t - 1)` are nonempty, pairwise disjoint
families of `d`-element subsets of `U`, and for `i < j < k < t`, every `S ∈ F i` and `T ∈ F k`
have `S ∩ T ⊆ R` for some `R ∈ F j`. Layers with index `≥ t` are ignored. -/
structure IsConnectedLayerFamily (d : ℕ) (U : Finset α) (F : ℕ → Finset (Finset α)) (t : ℕ) :
    Prop where
  nonempty : ∀ i < t, (F i).Nonempty
  disjoint : ∀ i < t, ∀ j < t, i ≠ j → Disjoint (F i) (F j)
  subset : ∀ i < t, ∀ S ∈ F i, S ⊆ U
  card : ∀ i < t, ∀ S ∈ F i, S.card = d
  connected : ∀ i j k, i < j → j < k → k < t → ∀ S ∈ F i, ∀ T ∈ F k, ∃ R ∈ F j, S ∩ T ⊆ R

namespace IsConnectedLayerFamily

variable {d : ℕ} {U : Finset α} {F : ℕ → Finset (Finset α)} {t : ℕ}

/-- The first `a ≤ t` layers form a connected layer family. -/
theorem truncate (h : IsConnectedLayerFamily d U F t) {a : ℕ} (ha : a ≤ t) :
    IsConnectedLayerFamily d U F a where
  nonempty i hi := h.nonempty i (by omega)
  disjoint i hi j hj := h.disjoint i (by omega) j (by omega)
  subset i hi := h.subset i (by omega)
  card i hi := h.card i (by omega)
  connected i j k hij hjk hk := h.connected i j k hij hjk (by omega)

/-- Replace the ground set by any set containing every set of every layer. -/
theorem restrict (h : IsConnectedLayerFamily d U F t) {W : Finset α}
    (hW : ∀ i < t, ∀ S ∈ F i, S ⊆ W) : IsConnectedLayerFamily d W F t where
  nonempty := h.nonempty
  disjoint := h.disjoint
  subset := hW
  card := h.card
  connected := h.connected

/-- The layers in reverse order form a connected layer family. -/
theorem reverse (h : IsConnectedLayerFamily d U F t) :
    IsConnectedLayerFamily d U (fun i => F (t - 1 - i)) t where
  nonempty i hi := h.nonempty _ (by omega)
  disjoint i hi j hj hij := h.disjoint _ (by omega) _ (by omega) (by omega)
  subset i hi := h.subset _ (by omega)
  card i hi := h.card _ (by omega)
  connected i j k hij hjk hk S hS T hT := by
    obtain ⟨R, hR, hsub⟩ := h.connected (t - 1 - k) (t - 1 - j) (t - 1 - i) (by omega)
      (by omega) (by omega) T hT S hS
    exact ⟨R, hR, by rw [Finset.inter_comm]; exact hsub⟩

/-- The link of an element `x`: if `x` lies in a set of layer `i` and in a set of layer `k`,
`i ≤ k < t`, then the layers `i, …, k`, restricted to the sets containing `x`, with `x` removed,
form a connected layer family of `(d - 1)`-sets on `U \ {x}` of length `k - i + 1`. -/
theorem link (h : IsConnectedLayerFamily d U F t) {x : α} {i k : ℕ} (hik : i ≤ k) (hk : k < t)
    {S T : Finset α} (hS : S ∈ F i) (hxS : x ∈ S) (hT : T ∈ F k) (hxT : x ∈ T) :
    IsConnectedLayerFamily (d - 1) (U.erase x)
      (fun l => ((F (i + l)).filter (fun A => x ∈ A)).image (fun A => A.erase x)) (k - i + 1) where
  nonempty l hl := by
    have key : ∃ R ∈ F (i + l), x ∈ R := by
      rcases Nat.eq_zero_or_pos l with rfl | hl0
      · exact ⟨S, by simpa using hS, hxS⟩
      · by_cases hlk : i + l = k
        · exact ⟨T, hlk ▸ hT, hxT⟩
        · obtain ⟨R, hR, hsub⟩ := h.connected i (i + l) k (by omega) (by omega) hk S hS T hT
          exact ⟨R, hR, hsub (Finset.mem_inter.2 ⟨hxS, hxT⟩)⟩
    obtain ⟨R, hR, hxR⟩ := key
    exact ⟨R.erase x, Finset.mem_image.2 ⟨R, Finset.mem_filter.2 ⟨hR, hxR⟩, rfl⟩⟩
  disjoint l₁ hl₁ l₂ hl₂ hl := by
    rw [Finset.disjoint_left]
    intro A hA₁ hA₂
    obtain ⟨S₁, hS₁, rfl⟩ := Finset.mem_image.1 hA₁
    obtain ⟨S₂, hS₂, he⟩ := Finset.mem_image.1 hA₂
    rw [Finset.mem_filter] at hS₁ hS₂
    have hS : S₂ = S₁ := by
      rw [← Finset.insert_erase hS₁.2, ← Finset.insert_erase hS₂.2, he]
    subst hS
    exact Finset.disjoint_left.1 (h.disjoint (i + l₁) (by omega) (i + l₂) (by omega) (by omega))
      hS₁.1 hS₂.1
  subset l hl A hA := by
    obtain ⟨S₁, hS₁, rfl⟩ := Finset.mem_image.1 hA
    exact Finset.erase_subset_erase x (h.subset _ (by omega) S₁ (Finset.mem_filter.1 hS₁).1)
  card l hl A hA := by
    obtain ⟨S₁, hS₁, rfl⟩ := Finset.mem_image.1 hA
    rw [Finset.mem_filter] at hS₁
    rw [Finset.card_erase_of_mem hS₁.2, h.card _ (by omega) S₁ hS₁.1]
  connected l₁ l₂ l₃ h₁₂ h₂₃ h₃ A hA B hB := by
    obtain ⟨S₁, hS₁, rfl⟩ := Finset.mem_image.1 hA
    obtain ⟨S₃, hS₃, rfl⟩ := Finset.mem_image.1 hB
    rw [Finset.mem_filter] at hS₁ hS₃
    obtain ⟨R, hR, hsub⟩ := h.connected (i + l₁) (i + l₂) (i + l₃) (by omega) (by omega)
      (by omega) S₁ hS₁.1 S₃ hS₃.1
    have hxR : x ∈ R := hsub (Finset.mem_inter.2 ⟨hS₁.2, hS₃.2⟩)
    refine ⟨R.erase x, Finset.mem_image.2 ⟨R, Finset.mem_filter.2 ⟨hR, hxR⟩, rfl⟩, ?_⟩
    intro y hy
    rw [Finset.mem_inter, Finset.mem_erase, Finset.mem_erase] at hy
    exact Finset.mem_erase.2 ⟨hy.1.1, hsub (Finset.mem_inter.2 ⟨hy.1.2, hy.2.2⟩)⟩

/-- For `d = 0` there is at most one layer (the only `0`-set is `∅`, and layers are disjoint). -/
theorem length_le_one_of_card_zero (h : IsConnectedLayerFamily 0 U F t) : t ≤ 1 := by
  by_contra ht
  obtain ⟨S, hS⟩ := h.nonempty 0 (by omega)
  obtain ⟨T, hT⟩ := h.nonempty 1 (by omega)
  have hS0 : S = ∅ := Finset.card_eq_zero.1 (h.card 0 (by omega) S hS)
  have hT0 : T = ∅ := Finset.card_eq_zero.1 (h.card 1 (by omega) T hT)
  subst hS0 hT0
  exact Finset.disjoint_left.1 (h.disjoint 0 (by omega) 1 (by omega) (by omega)) hS hT

/-- On an empty ground set there are no layers of nonempty sets. -/
theorem length_eq_zero_of_card_eq_zero (h : IsConnectedLayerFamily d U F t) (hd : 1 ≤ d)
    (hU : U.card = 0) : t = 0 := by
  by_contra ht
  obtain ⟨S, hS⟩ := h.nonempty 0 (by omega)
  have h1 := h.card 0 (by omega) S hS
  have h2 := Finset.card_le_card (h.subset 0 (by omega) S hS)
  omega

/-- The elements used by the first `k` layers. -/
def usedPrefix (F : ℕ → Finset (Finset α)) (k : ℕ) : Finset α :=
  (Finset.range k).biUnion fun i => (F i).biUnion id

theorem mem_usedPrefix {k : ℕ} {x : α} :
    x ∈ usedPrefix F k ↔ ∃ i < k, ∃ S ∈ F i, x ∈ S := by
  simp [usedPrefix]

theorem usedPrefix_subset (h : IsConnectedLayerFamily d U F t) {k : ℕ} (hk : k ≤ t) :
    usedPrefix F k ⊆ U := by
  intro x hx
  obtain ⟨i, hi, S, hS, hxS⟩ := mem_usedPrefix.1 hx
  exact h.subset i (by omega) S hS hxS

/-- The longest prefix using at most `m` elements has length at most `g`, if `g` bounds every
family of the same `d` on at most `m` elements. If it is shorter than the family, the next
layer brings the number of used elements above `m`. -/
theorem exists_prefix (h : IsConnectedLayerFamily d U F t) {m g : ℕ}
    (hg : ∀ (W : Finset α) (s : ℕ), W.card ≤ m → IsConnectedLayerFamily d W F s → s ≤ g) :
    ∃ a ≤ t, a ≤ g ∧ (a < t → m < (usedPrefix F (a + 1)).card) := by
  classical
  let P : ℕ → Prop := fun k => (usedPrefix F k).card ≤ m
  refine ⟨Nat.findGreatest P t, Nat.findGreatest_le t, ?_, fun hlt => ?_⟩
  · have hP : P (Nat.findGreatest P t) :=
      Nat.findGreatest_spec (P := P) (Nat.zero_le t) (by simp [P, usedPrefix])
    refine hg _ _ hP ((h.truncate (Nat.findGreatest_le t)).restrict ?_)
    intro i hi S hS x hx
    exact mem_usedPrefix.2 ⟨i, hi, S, hS, hx⟩
  · have := Nat.findGreatest_is_greatest (P := P) (n := t) (Nat.lt_succ_self _) (by omega)
    simp only [P, not_le] at this
    exact this

/-- **Kalai–Kleitman style recursion.** Let `g` bound the length of every connected layer
family of `d`-sets on at most `m` elements, and `h'` bound the length of every family of
`(d - 1)`-sets on at most `n - 1` elements. Then a family of `d`-sets on `U` with
`U.card ≤ n ≤ 2 m + 1` has length at most `2 g + h'`. -/
theorem length_le_two_mul_add (h : IsConnectedLayerFamily d U F t) {n m g h' : ℕ}
    (hU : U.card ≤ n) (hnm : n ≤ 2 * m + 1)
    (hg : ∀ (W : Finset α) (G : ℕ → Finset (Finset α)) (s : ℕ), W.card ≤ m →
      IsConnectedLayerFamily d W G s → s ≤ g)
    (hh : ∀ (W : Finset α) (G : ℕ → Finset (Finset α)) (s : ℕ), W.card ≤ n - 1 →
      IsConnectedLayerFamily (d - 1) W G s → s ≤ h') :
    t ≤ 2 * g + h' := by
  obtain ⟨a, hat, hag, ha⟩ := h.exists_prefix (fun W s hW hs => hg W F s hW hs)
  obtain ⟨b, hbt, hbg, hb⟩ := h.reverse.exists_prefix (fun W s hW hs => hg W _ s hW hs)
  by_cases hab : t ≤ a + b
  · omega
  have h1 := ha (by omega)
  have h2 := hb (by omega)
  have hsub1 := h.usedPrefix_subset (k := a + 1) (by omega)
  have hsub2 := h.reverse.usedPrefix_subset (k := b + 1) (by omega)
  obtain ⟨x, hx1, hx2⟩ : ∃ x, x ∈ usedPrefix F (a + 1) ∧
      x ∈ usedPrefix (fun i => F (t - 1 - i)) (b + 1) := by
    by_contra hne
    push Not at hne
    have hdisj : Disjoint (usedPrefix F (a + 1)) (usedPrefix (fun i => F (t - 1 - i)) (b + 1)) :=
      Finset.disjoint_left.2 hne
    have := Finset.card_le_card (Finset.union_subset hsub1 hsub2)
    rw [Finset.card_union_of_disjoint hdisj] at this
    omega
  obtain ⟨i, hi, S, hS, hxS⟩ := mem_usedPrefix.1 hx1
  obtain ⟨j, hj, T, hT, hxT⟩ := mem_usedPrefix.1 hx2
  have hlink := h.link (i := i) (k := t - 1 - j) (by omega) (by omega) hS hxS hT hxT
  have hcard : (U.erase x).card ≤ n - 1 := by
    rw [Finset.card_erase_of_mem (hsub1 hx1)]
    omega
  have := hh _ _ _ hcard hlink
  omega

/-- Arithmetic for the inductive step of `length_le`. -/
private theorem step_arith (d n : ℕ) (hn : 1 ≤ n) (h' : ℕ)
    (hh : h' ≤ if d = 0 then 1 else (n - 1) * (d + 1) ^ Nat.log 2 (n - 1)) :
    2 * (n / 2 * (d + 2) ^ Nat.log 2 (n / 2)) + h' ≤ n * (d + 2) ^ Nat.log 2 n := by
  rcases Nat.eq_or_lt_of_le hn with rfl | hn2
  · split_ifs at hh with hd <;> simp_all
  have hL : 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by rw [pow_one]; omega)
  rw [Nat.log_div_base]
  obtain ⟨L, hLeq⟩ : ∃ L, Nat.log 2 n = L + 1 := ⟨Nat.log 2 n - 1, by omega⟩
  rw [hLeq, Nat.add_sub_cancel]
  have h2m : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
  have hA : 2 * (n / 2 * (d + 2) ^ L) ≤ n * (d + 2) ^ L := by
    rw [← mul_assoc]; exact Nat.mul_le_mul_right _ h2m
  have hB : h' ≤ n * (d + 1) * (d + 2) ^ L := by
    split_ifs at hh with hd
    · subst hd
      have h3 : 1 * 1 ≤ n * 2 ^ L := Nat.mul_le_mul (by omega) Nat.one_le_two_pow
      simp only [zero_add, mul_one]
      linarith
    · have hlog : Nat.log 2 (n - 1) ≤ L + 1 := hLeq ▸ Nat.log_mono_right (by omega)
      calc h' ≤ (n - 1) * (d + 1) ^ Nat.log 2 (n - 1) := hh
        _ ≤ n * (d + 1) ^ (L + 1) :=
          Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) hlog)
        _ = n * (d + 1) * (d + 1) ^ L := by ring
        _ ≤ n * (d + 1) * (d + 2) ^ L :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) L)
  calc 2 * (n / 2 * (d + 2) ^ L) + h' ≤ n * (d + 2) ^ L + n * (d + 1) * (d + 2) ^ L :=
        Nat.add_le_add hA hB
    _ = n * (d + 2) ^ (L + 1) := by ring

/-- **Quasi-polynomial bound.** A connected layer family of `d`-sets, `d ≥ 1`, on a ground set
with at most `n` elements has length at most `n * (d + 1) ^ ⌊log₂ n⌋`. -/
theorem length_le {d n : ℕ} (hd : 1 ≤ d) {U : Finset α} {F : ℕ → Finset (Finset α)} {t : ℕ}
    (hU : U.card ≤ n) (h : IsConnectedLayerFamily d U F t) :
    t ≤ n * (d + 1) ^ Nat.log 2 n := by
  obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  clear hd
  induction d generalizing n U F t with
  | zero =>
    induction n using Nat.strong_induction_on generalizing U F t with
    | _ n ihn =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [h.length_eq_zero_of_card_eq_zero (by omega) (by omega)]
      have := h.length_le_two_mul_add (m := n / 2) hU (by omega)
        (fun W G s hW hs => ihn (n / 2) (by omega) hW hs)
        (fun W G s _ hs => hs.length_le_one_of_card_zero)
      exact this.trans (step_arith 0 n hn 1 (by simp))
  | succ d ihd =>
    induction n using Nat.strong_induction_on generalizing U F t with
    | _ n ihn =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [h.length_eq_zero_of_card_eq_zero (by omega) (by omega)]
      have := h.length_le_two_mul_add (m := n / 2) hU (by omega)
        (fun W G s hW hs => ihn (n / 2) (by omega) hW hs)
        (fun W G s hW hs => ihd hW hs)
      exact this.trans (step_arith (d + 1) n hn _ (by simp))

/-- `(a ^ logb 2 b) = (b ^ logb 2 a)` for positive reals. -/
private theorem rpow_logb_swap {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a ^ Real.logb 2 b = b ^ Real.logb 2 a := by
  rw [Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hb, Real.logb, Real.logb]
  congr 1
  ring

/-- **Quasi-polynomial bound, real form.** For `d ≥ 1` and `U.card ≤ n`,
`t ≤ n ^ (1 + log₂ (d + 1))`. -/
theorem length_le_rpow {d n : ℕ} (hd : 1 ≤ d) {U : Finset α} {F : ℕ → Finset (Finset α)}
    {t : ℕ} (hU : U.card ≤ n) (h : IsConnectedLayerFamily d U F t) :
    (t : ℝ) ≤ (n : ℝ) ^ (1 + Real.logb 2 (d + 1)) := by
  have ht := h.length_le hd hU
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : t = 0 := by simpa using ht
    simp only [this, CharP.cast_eq_zero]
    exact Real.rpow_nonneg le_rfl _
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hd1 : (1 : ℝ) ≤ (d : ℝ) + 1 := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  calc (t : ℝ) ≤ ((n * (d + 1) ^ Nat.log 2 n : ℕ) : ℝ) := by exact_mod_cast ht
    _ = (n : ℝ) * ((d : ℝ) + 1) ^ ((Nat.log 2 n : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]; push_cast; ring
    _ ≤ (n : ℝ) * ((d : ℝ) + 1) ^ Real.logb 2 n := by
        gcongr
        exact Real.natLog_le_logb n 2
    _ = (n : ℝ) * (n : ℝ) ^ Real.logb 2 ((d : ℝ) + 1) := by
        rw [rpow_logb_swap (by linarith) hnR]
    _ = (n : ℝ) ^ (1 + Real.logb 2 ((d : ℝ) + 1)) := by
        rw [Real.rpow_add hnR, Real.rpow_one]

end IsConnectedLayerFamily

/-- **The hypotheses are satisfiable; a lower bound of Hirsch type.** For `1 ≤ d ≤ n`, the
sliding windows `{i, i + 1, …, i + d - 1}`, one per layer, `i = 0, …, n - d`, form a connected
layer family of `d`-subsets of `{0, …, n - 1}` of length `n - d + 1`. -/
theorem isConnectedLayerFamily_window {d n : ℕ} (hd : 1 ≤ d) (hdn : d ≤ n) :
    IsConnectedLayerFamily d (Finset.range n) (fun i => {Finset.Ico i (i + d)}) (n - d + 1) where
  nonempty i _ := Finset.singleton_nonempty _
  disjoint i _ j _ hij := by
    rw [Finset.disjoint_singleton]
    intro heq
    have h1 : i ∈ Finset.Ico j (j + d) := heq ▸ Finset.mem_Ico.2 ⟨le_rfl, by omega⟩
    have h2 : j ∈ Finset.Ico i (i + d) := heq ▸ Finset.mem_Ico.2 ⟨le_rfl, by omega⟩
    rw [Finset.mem_Ico] at h1 h2
    omega
  subset i hi S hS := by
    rw [Finset.mem_singleton] at hS
    subst hS
    intro y hy
    rw [Finset.mem_Ico] at hy
    rw [Finset.mem_range]
    omega
  card i _ S hS := by
    rw [Finset.mem_singleton] at hS
    subst hS
    simp
  connected i j k hij hjk _ S hS T hT := by
    rw [Finset.mem_singleton] at hS hT
    subst hS hT
    refine ⟨_, Finset.mem_singleton_self _, fun y hy => ?_⟩
    rw [Finset.mem_inter, Finset.mem_Ico, Finset.mem_Ico] at hy
    rw [Finset.mem_Ico]
    omega

end Applied.Optimization
