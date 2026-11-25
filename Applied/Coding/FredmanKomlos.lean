import Applied.Coding.Hansel
import Applied.Coding.PerfectHash
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.CardEmbedding

/-!
# The Fredman–Komlós bound for perfect `k`-hash codes

A code `C ⊆ {0,…,k-1}ⁿ` is a perfect `k`-hash code (`IsPerfectHashCode`) if any `k` distinct
codewords take `k` pairwise distinct values in some coordinate. The main result,
`IsPerfectHashCode.fredmanKomlos`, is the Fredman–Komlós bound in the finite form
`N (N-1) ⋯ (N-k+2) · k^{k-1} · log₂ (N-k+2) ≤ n · k! · N^{k-1}` (`k ≥ 2`, `N = |C|`), proved by
the reduction to Hansel's lemma (`Applied/Coding/Hansel.lean`): for `k - 2` fixed distinct
codewords, the coordinates where they are pairwise distinct leave two free symbols, which
split the other codewords into a complete bipartite graph; these graphs cover all pairs. Averaging
over the choice of the `k - 2` codewords and bounding, coordinate by coordinate, the number of
`(k-1)`-tuples with pairwise distinct symbols by Maclaurin's inequality gives the bound.

## Elementary symmetric polynomial of degree `|A| - 1`

* `esymmTop A m = ∑_{a ∈ A} ∏_{b ∈ A \ {a}} m b`.
* `prod_le_avg_pow`: AM-GM, `∏_{a ∈ A} m a ≤ (S / |A|)^{|A|}` with `S = ∑_{a ∈ A} m a`.
* `esymmTop_le`: the top-degree case of Maclaurin's inequality,
  `esymmTop A m ≤ |A| (S / |A|)^{|A| - 1}` for nonnegative `m`.
* `injSum m A j = ∑` over injective `g : Fin j → ι` with values in `A` of `∏_t m (g t)`, and
  `injSum_eq`: `injSum m A j = j! · esymmTop A m` when `|A| = j + 1`; `injSum_univ_le`.
* `card_filter_injective_comp`: the number of `j`-tuples of elements of a finite type `β` whose
  images under `φ : β → ι` are pairwise distinct is `injSum (fiber sizes of φ) univ j`.

## The bound

* `hansel_fkFree`: Hansel's lemma applied to one tuple of `k - 2` distinct codewords.
* `sum_card_fkFree`: summing over all tuples.
* `fredmanKomlos_core`: the bound for an abstract finite family of codewords.
* `IsPerfectHashCode.fredmanKomlos`: the bound for perfect `k`-hash codes.
-/

open Finset

namespace Applied.Coding

section Symmetric

variable {ι : Type*} [DecidableEq ι]

/-- The elementary symmetric polynomial of degree `|A| - 1` in the values `m a`, `a ∈ A`. -/
noncomputable def esymmTop (A : Finset ι) (m : ι → ℝ) : ℝ := ∑ a ∈ A, ∏ b ∈ A.erase a, m b

/-- `esymmTop` of the empty family is `0`. -/
theorem esymmTop_empty (m : ι → ℝ) : esymmTop ∅ m = 0 := by simp [esymmTop]

/-- Recursion for `esymmTop`: adding a new index `j` to `s` gives
`e_{|s|}(insert j s) = ∏_{b ∈ s} m b + m j · e_{|s|-1}(s)`. -/
theorem esymmTop_insert {j : ι} {s : Finset ι} (hj : j ∉ s) (m : ι → ℝ) :
    esymmTop (insert j s) m = ∏ b ∈ s, m b + m j * esymmTop s m := by
  rw [esymmTop, sum_insert hj, erase_insert hj, esymmTop, mul_sum]
  congr 1
  refine sum_congr rfl fun a ha => ?_
  have hne : j ≠ a := fun h => hj (h ▸ ha)
  rw [erase_insert_of_ne hne, prod_insert (fun h => hj (mem_of_mem_erase h))]

/-- One step of AM-GM: `b aʳ ≤ ((r a + b) / (r + 1))^{r+1}` for `a, b ≥ 0`. -/
private lemma amgm_step (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (r : ℕ) :
    b * a ^ r ≤ ((r * a + b) / (r + 1)) ^ (r + 1) := by
  rcases ha.eq_or_lt with rfl | ha
  · rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp
    · rw [zero_pow hr.ne', mul_zero]; positivity
  have hr1 : (0 : ℝ) < r + 1 := by positivity
  set x := (b - a) / ((r + 1) * a) with hx
  have hx2 : -2 ≤ x := by
    rw [hx, le_div_iff₀ (by positivity)]
    nlinarith
  have hbern := one_add_mul_le_pow hx2 (r + 1)
  have heq : (r * a + b) / (r + 1) = a * (1 + x) := by
    rw [hx]; field_simp; ring
  rw [heq, mul_pow]
  have h1 : (1 : ℝ) + ((r + 1 : ℕ) : ℝ) * x = b / a := by
    rw [hx]; push_cast; field_simp; ring
  rw [h1] at hbern
  calc b * a ^ r = a ^ (r + 1) * (b / a) := by field_simp; ring
    _ ≤ a ^ (r + 1) * (1 + x) ^ (r + 1) := mul_le_mul_of_nonneg_left hbern (by positivity)

/-- **AM-GM**: `∏_{a ∈ A} m a ≤ ((∑_{a ∈ A} m a) / |A|)^{|A|}` for nonnegative `m`. -/
theorem prod_le_avg_pow (m : ι → ℝ) : ∀ (A : Finset ι), (∀ a ∈ A, 0 ≤ m a) →
    ∏ a ∈ A, m a ≤ ((∑ a ∈ A, m a) / A.card) ^ A.card := by
  intro A
  induction A using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    intro hm
    have hs : ∀ a ∈ s, 0 ≤ m a := fun a ha => hm a (mem_insert_of_mem ha)
    have hmj : 0 ≤ m j := hm j (mem_insert_self j s)
    rw [prod_insert hj, sum_insert hj, card_insert_of_notMem hj]
    set r := s.card
    set S := ∑ a ∈ s, m a
    have hS0 : 0 ≤ S := sum_nonneg hs
    have hSr : S = r * (S / r) := by
      rcases Nat.eq_zero_or_pos r with h | h
      · have : s = ∅ := card_eq_zero.mp h
        have hS : S = 0 := by rw [show S = ∑ a ∈ s, m a from rfl, this, sum_empty]
        rw [hS, zero_div, mul_zero]
      · field_simp
    have ha : 0 ≤ S / r := div_nonneg hS0 (Nat.cast_nonneg _)
    calc m j * ∏ a ∈ s, m a ≤ m j * (S / r) ^ r := mul_le_mul_of_nonneg_left (ih hs) hmj
      _ ≤ ((r * (S / r) + m j) / (r + 1)) ^ (r + 1) := amgm_step _ _ ha hmj r
      _ = ((m j + S) / ((r + 1 : ℕ) : ℝ)) ^ (r + 1) := by rw [← hSr]; push_cast; ring_nf

/-- The step of the Maclaurin-type bound: `aʳ⁺¹ + b (r+1) aʳ ≤ (r+2) (((r+1) a + b)/(r+2))ʳ⁺¹`. -/
private lemma maclaurin_step (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (r : ℕ) :
    a ^ (r + 1) + b * ((r + 1) * a ^ r) ≤
      (r + 2) * (((r + 1) * a + b) / (r + 2)) ^ (r + 1) := by
  rcases ha.eq_or_lt with rfl | ha
  · rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp; field_simp; linarith
    · rw [zero_pow hr.ne', zero_pow (by omega)]; simp; positivity
  have hr2 : (0 : ℝ) < r + 2 := by positivity
  set x := (b - a) / ((r + 2) * a) with hx
  have hx2 : -2 ≤ x := by
    rw [hx, le_div_iff₀ (by positivity)]
    nlinarith
  have hbern := one_add_mul_le_pow hx2 (r + 1)
  have heq : ((r + 1) * a + b) / (r + 2) = a * (1 + x) := by
    rw [hx]; field_simp; ring
  rw [heq, mul_pow]
  have key : a ^ (r + 1) + b * ((r + 1) * a ^ r) =
      (r + 2) * a ^ (r + 1) * (1 + ((r + 1 : ℕ) : ℝ) * x) := by
    rw [hx]; push_cast; field_simp; ring
  rw [key, mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbern (by positivity))
    (by positivity)

/-- **Maclaurin's inequality, top degree**: for nonnegative `m`,
`esymmTop A m ≤ |A| (S / |A|)^{|A| - 1}` with `S = ∑_{a ∈ A} m a`. -/
theorem esymmTop_le (m : ι → ℝ) : ∀ (A : Finset ι), (∀ a ∈ A, 0 ≤ m a) →
    esymmTop A m ≤ A.card * ((∑ a ∈ A, m a) / A.card) ^ (A.card - 1) := by
  intro A
  induction A using Finset.induction_on with
  | empty => simp [esymmTop_empty]
  | insert j s hj ih =>
    intro hm
    have hs : ∀ a ∈ s, 0 ≤ m a := fun a ha => hm a (mem_insert_of_mem ha)
    have hmj : 0 ≤ m j := hm j (mem_insert_self j s)
    rw [esymmTop_insert hj, sum_insert hj, card_insert_of_notMem hj]
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp [esymmTop_empty]
    obtain ⟨q, hq⟩ : ∃ q, s.card = q + 1 := ⟨s.card - 1, by have := hne.card_pos; omega⟩
    have ih' := ih hs
    rw [hq] at ih' ⊢
    simp only [Nat.add_sub_cancel] at ih' ⊢
    set S := ∑ a ∈ s, m a
    have hS0 : 0 ≤ S := sum_nonneg hs
    have ha : 0 ≤ S / ((q + 1 : ℕ) : ℝ) := by positivity
    have hp := prod_le_avg_pow m s hs
    rw [hq] at hp
    have hSr : ((q + 1 : ℕ) : ℝ) * (S / ((q + 1 : ℕ) : ℝ)) = S := by field_simp
    have hstep := maclaurin_step (S / ((q + 1 : ℕ) : ℝ)) (m j) ha hmj q
    have hcast : ((q : ℝ) + 1) * (S / ((q + 1 : ℕ) : ℝ)) = S := by
      push_cast; field_simp
    rw [hcast] at hstep
    calc ∏ b ∈ s, m b + m j * esymmTop s m
        ≤ (S / ((q + 1 : ℕ) : ℝ)) ^ (q + 1) +
            m j * (((q + 1 : ℕ) : ℝ) * (S / ((q + 1 : ℕ) : ℝ)) ^ q) :=
          add_le_add hp (mul_le_mul_of_nonneg_left ih' hmj)
      _ ≤ (q + 2) * ((S + m j) / (q + 2)) ^ (q + 1) := by
          push_cast at hstep ⊢
          exact hstep
      _ = ((q + 1 + 1 : ℕ) : ℝ) * ((m j + S) / ((q + 1 + 1 : ℕ) : ℝ)) ^ (q + 1) := by
          push_cast; ring_nf

/-- `∑_{a ∈ A} m a · esymmTop (A \ {a}) m = (|A| - 1) · esymmTop A m`. -/
theorem sum_mul_esymmTop_erase (A : Finset ι) (m : ι → ℝ) :
    ∑ a ∈ A, m a * esymmTop (A.erase a) m = ((A.card - 1 : ℕ) : ℝ) * esymmTop A m := by
  simp only [esymmTop, mul_sum]
  rw [sum_comm' (t' := A) (s' := fun b => A.erase b)
    (f := fun a b => m a * ∏ c ∈ (A.erase a).erase b, m c)]
  · refine sum_congr rfl fun b hb => ?_
    have : ∀ a ∈ A.erase b, m a * ∏ c ∈ (A.erase a).erase b, m c = ∏ c ∈ A.erase b, m c := by
      intro a ha
      rw [erase_right_comm, mul_prod_erase _ _ ha]
    rw [sum_congr rfl this, sum_const, card_erase_of_mem hb, nsmul_eq_mul]
  · intro a b
    simp only [mem_erase]
    tauto

end Symmetric

section InjSum

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `∑` over injective maps `g : Fin j → ι` with values in `A` of `∏_t m (g t)`. -/
noncomputable def injSum (m : ι → ℝ) (A : Finset ι) (j : ℕ) : ℝ :=
  ∑ g : Fin j → ι, if Function.Injective g ∧ ∀ t, g t ∈ A then ∏ t, m (g t) else 0

omit [Fintype ι] in
private lemma cons_cond (A : Finset ι) {j : ℕ} (a : ι) (g : Fin j → ι) :
    (Function.Injective (Fin.cons a g : Fin (j + 1) → ι) ∧ ∀ t, (Fin.cons a g : Fin (j + 1) → ι) t ∈ A)
      ↔ a ∈ A ∧ (Function.Injective g ∧ ∀ t, g t ∈ A.erase a) := by
  rw [Fin.cons_injective_iff, Fin.forall_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Set.mem_range, not_exists, mem_erase]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨h3, h2, fun t => ⟨fun e => h1 t e, h4 t⟩⟩
  · rintro ⟨h3, h2, h4⟩
    exact ⟨⟨fun t e => (h4 t).1 e, h2⟩, h3, fun t => (h4 t).2⟩

/-- Recursion for `injSum` on the first coordinate of the injective tuple: choose its first
entry `a ∈ A`, then an injective `j`-tuple in `A.erase a`. -/
theorem injSum_succ (m : ι → ℝ) (A : Finset ι) (j : ℕ) :
    injSum m A (j + 1) = ∑ a ∈ A, m a * injSum m (A.erase a) j := by
  rw [injSum, ← (Fin.consEquiv fun _ => ι).sum_comp, Fintype.sum_prod_type,
    ← sum_filter_add_sum_filter_not univ (· ∈ A), filter_mem_eq_inter, univ_inter]
  have h0 : ∑ a ∈ univ.filter (· ∉ A), ∑ g : Fin j → ι,
      (if Function.Injective ((Fin.consEquiv fun _ => ι) (a, g)) ∧
          ∀ t, (Fin.consEquiv fun _ => ι) (a, g) t ∈ A
        then ∏ t, m ((Fin.consEquiv fun _ => ι) (a, g) t) else 0) = 0 := by
    refine sum_eq_zero fun a ha => sum_eq_zero fun g _ => ?_
    have ha' : a ∉ A := (mem_filter.mp ha).2
    rw [ite_eq_right]
    intro h
    exact ha' ((cons_cond A a g).mp h).1
  rw [h0, add_zero]
  refine sum_congr rfl fun a ha => ?_
  rw [injSum, mul_sum]
  refine sum_congr rfl fun g _ => ?_
  have hc : (Fin.consEquiv fun _ => ι) (a, g) = Fin.cons a g := rfl
  rw [hc]
  by_cases h : Function.Injective g ∧ ∀ t, g t ∈ A.erase a
  · rw [ite_eq_left ((cons_cond A a g).mpr ⟨ha, h⟩), ite_eq_left h, Fin.prod_univ_succ]
    simp
  · rw [ite_eq_right (fun h' => h ((cons_cond A a g).mp h').2), ite_eq_right h, mul_zero]

/-- `injSum m A j = j! · esymmTop A m` when `|A| = j + 1`. -/
theorem injSum_eq (m : ι → ℝ) : ∀ (j : ℕ) (A : Finset ι), A.card = j + 1 →
    injSum m A j = j.factorial * esymmTop A m
  | 0, A, hA => by
    obtain ⟨a, rfl⟩ := card_eq_one.mp hA
    simp [injSum, esymmTop, Function.injective_of_subsingleton]
  | j + 1, A, hA => by
    rw [injSum_succ]
    have : ∀ a ∈ A, m a * injSum m (A.erase a) j = j.factorial * (m a * esymmTop (A.erase a) m) := by
      intro a ha
      rw [injSum_eq m j (A.erase a) (by rw [card_erase_of_mem ha, hA]; rfl)]
      ring
    rw [sum_congr rfl this, ← mul_sum, sum_mul_esymmTop_erase, hA, Nat.factorial_succ]
    rw [Nat.add_sub_cancel]
    push_cast
    ring

/-- The bound `injSum m univ (k - 1) ≤ k! (S / k)^{k-1}` for nonnegative `m`, where
`k = |ι| ≥ 1` and `S = ∑ m`. -/
theorem injSum_univ_le (m : ι → ℝ) (hm : ∀ a, 0 ≤ m a) {k : ℕ} (hk : Fintype.card ι = k + 1) :
    injSum m univ k ≤ (k + 1).factorial * ((∑ a, m a) / (k + 1 : ℕ)) ^ k := by
  rw [injSum_eq m k univ (by rw [card_univ, hk])]
  have h := esymmTop_le m univ (fun a _ => hm a)
  rw [card_univ, hk, Nat.add_sub_cancel] at h
  rw [Nat.factorial_succ]
  push_cast at h ⊢
  calc (k.factorial : ℝ) * esymmTop univ m
      ≤ k.factorial * ((k + 1) * ((∑ a, m a) / (k + 1)) ^ k) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = (k + 1) * k.factorial * ((∑ a, m a) / (k + 1)) ^ k := by ring

/-- Counting tuples with pairwise distinct images: for `φ : β → ι`, the number of
`f : Fin j → β` with `φ ∘ f` injective is `injSum (fiber sizes of φ) univ j`. -/
theorem card_filter_injective_comp {β : Type*} [Fintype β] [DecidableEq β] (φ : β → ι)
    (j : ℕ) :
    (((univ : Finset (Fin j → β)).filter fun f => Function.Injective (φ ∘ f)).card : ℝ) =
      injSum (fun s => ((univ.filter fun b => φ b = s).card : ℝ)) univ j := by
  classical
  rw [card_eq_sum_card_fiberwise (f := fun f => φ ∘ f) (t := univ)
    (fun _ _ => mem_coe.mpr (mem_univ _)), injSum]
  push_cast
  refine sum_congr rfl fun g _ => ?_
  simp only [mem_univ, implies_true, and_true]
  by_cases hg : Function.Injective g
  · rw [ite_eq_left hg]
    have : ((univ.filter fun f : Fin j → β => Function.Injective (φ ∘ f)).filter
        fun f => φ ∘ f = g) =
        Fintype.piFinset fun t => univ.filter fun b => φ b = g t := by
      ext f
      simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
      constructor
      · rintro ⟨-, h⟩ t
        rw [← h]; rfl
      · intro h
        have hfg : φ ∘ f = g := funext h
        exact ⟨hfg ▸ hg, hfg⟩
    rw [this, Fintype.card_piFinset]
    push_cast
    rfl
  · rw [ite_eq_right hg]
    have : ((univ.filter fun f : Fin j → β => Function.Injective (φ ∘ f)).filter
        fun f => φ ∘ f = g) = ∅ := by
      ext f
      simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false, not_and]
      intro h hfg
      exact hg (hfg ▸ h)
    rw [this]
    simp

end InjSum

section FK

variable {β : Type*} [Fintype β] [DecidableEq β] {n : ℕ}

/-- For a tuple `c` of codewords and a coordinate `i`: the codewords `x` such that the symbols
`c₁(i), …, c_m(i), x(i)` are pairwise distinct. -/
noncomputable def fkFree {m k : ℕ} (w : β → Fin n → Fin k) (c : Fin m → β) (i : Fin n) :
    Finset β :=
  univ.filter fun x => Function.Injective (fun t => w (c t) i) ∧
    w x i ∉ univ.image (fun t => w (c t) i)

/-- **Hansel's lemma applied to one tuple** (the reduction of Fredman and Komlós). Fix `m`
distinct codewords `c₁, …, c_m` of a perfect `(m+2)`-hash family. For every coordinate where
their symbols are distinct, two symbols remain; the codewords taking these two symbols form a
complete bipartite graph on the other codewords, and these graphs cover all pairs. -/
theorem hansel_fkFree {m : ℕ} (w : β → Fin n → Fin (m + 2))
    (H : ∀ S : Finset β, S.card = m + 2 → ∃ i, Set.InjOn (fun b => w b i) S)
    (c : Fin m → β) (hc : Function.Injective c) :
    ((Fintype.card β - m : ℕ) : ℝ) * Real.logb 2 ((Fintype.card β - m : ℕ) : ℝ) ≤
      ∑ i, ((fkFree w c i).card : ℝ) := by
  classical
  set V : Finset β := univ \ univ.image c with hVdef
  have hV : V.card = Fintype.card β - m := by
    rw [hVdef, card_sdiff_of_subset (subset_univ _), card_univ, card_image_of_injective _ hc,
      card_univ, Fintype.card_fin]
  set A : Fin n → Finset (Fin (m + 2)) := fun i => univ.image (fun t => w (c t) i) with hA
  set X : Fin n → Finset β := fun i => V.filter fun x => Function.Injective (fun t => w (c t) i) ∧
    w x i ∉ A i ∧ ∀ y, y ∉ A i → w x i ≤ y with hX
  set Y : Fin n → Finset β := fun i => V.filter fun x => Function.Injective (fun t => w (c t) i) ∧
    w x i ∉ A i ∧ ∃ y, y ∉ A i ∧ y < w x i with hY
  have hdisj : ∀ i ∈ (univ : Finset (Fin n)), Disjoint (X i) (Y i) := by
    intro i _
    rw [disjoint_left]
    intro x hx hy
    obtain ⟨-, -, -, hle⟩ := mem_filter.mp hx
    obtain ⟨-, -, -, y, hy, hlt⟩ := mem_filter.mp hy
    exact absurd (hle y hy) (not_le.mpr hlt)
  have hcov : BicliqueCover V univ X Y := by
    intro u hu v hv huv
    have hu' : u ∉ univ.image c := (mem_sdiff.mp hu).2
    have hv' : v ∉ univ.image c := (mem_sdiff.mp hv).2
    set S := insert u (insert v (univ.image c)) with hS
    have hScard : S.card = m + 2 := by
      rw [hS, card_insert_of_notMem, card_insert_of_notMem hv', card_image_of_injective _ hc,
        card_univ, Fintype.card_fin]
      simp only [mem_insert, not_or]
      exact ⟨huv, hu'⟩
    obtain ⟨i, hi⟩ := H S hScard
    have hcS : ∀ t, c t ∈ S := fun t => by
      rw [hS]; exact mem_insert_of_mem (mem_insert_of_mem (mem_image_of_mem _ (mem_univ t)))
    have huS : u ∈ S := mem_insert_self _ _
    have hvS : v ∈ S := mem_insert_of_mem (mem_insert_self _ _)
    have hinj : Function.Injective (fun t => w (c t) i) :=
      fun t t' e => hc (hi (mem_coe.mpr (hcS t)) (mem_coe.mpr (hcS t')) e)
    have hnot : ∀ x ∈ S, x ∉ univ.image c → w x i ∉ A i := by
      intro x hx hx' hmem
      obtain ⟨t, -, e⟩ := mem_image.mp hmem
      exact hx' (mem_image.mpr ⟨t, mem_univ _, hi (mem_coe.mpr (hcS t)) (mem_coe.mpr hx) e⟩)
    have hua := hnot u huS hu'
    have hva := hnot v hvS hv'
    have huv' : w u i ≠ w v i := fun e => huv (hi (mem_coe.mpr huS) (mem_coe.mpr hvS) e)
    have hAcard : (A i).card = m := by
      rw [hA]; simp only
      rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
    have hcompl : ({w u i, w v i} : Finset (Fin (m + 2))) = univ \ A i := by
      apply eq_of_subset_of_card_le
      · intro y hy
        simp only [mem_insert, mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact mem_sdiff.mpr ⟨mem_univ _, hua⟩
        · exact mem_sdiff.mpr ⟨mem_univ _, hva⟩
      · rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin, hAcard,
          card_pair huv']
        omega
    have hrest : ∀ y, y ∉ A i → y = w u i ∨ y = w v i := by
      intro y hy
      have : y ∈ ({w u i, w v i} : Finset (Fin (m + 2))) := by
        rw [hcompl]; exact mem_sdiff.mpr ⟨mem_univ _, hy⟩
      simpa using this
    refine ⟨i, mem_univ _, ?_⟩
    rcases lt_or_gt_of_ne huv' with h | h
    · left
      refine ⟨mem_filter.mpr ⟨hu, hinj, hua, fun y hy => ?_⟩,
        mem_filter.mpr ⟨hv, hinj, hva, w u i, hua, h⟩⟩
      rcases hrest y hy with rfl | rfl
      · exact le_rfl
      · exact h.le
    · right
      refine ⟨mem_filter.mpr ⟨hv, hinj, hva, fun y hy => ?_⟩,
        mem_filter.mpr ⟨hu, hinj, hua, w v i, hva, h⟩⟩
      rcases hrest y hy with rfl | rfl
      · exact h.le
      · exact le_rfl
  have hh := hansel V univ X Y hdisj hcov
  rw [hV] at hh
  refine hh.trans (sum_le_sum fun i _ => ?_)
  have hsub : (V.filter fun v => v ∈ X i ∨ v ∈ Y i) ⊆ fkFree w c i := by
    intro x hx
    rw [mem_filter] at hx
    rw [fkFree, mem_filter]
    rcases hx.2 with h | h
    · obtain ⟨-, h1, h2, -⟩ := mem_filter.mp h
      exact ⟨mem_univ _, h1, h2⟩
    · obtain ⟨-, h1, h2, -⟩ := mem_filter.mp h
      exact ⟨mem_univ _, h1, h2⟩
  exact_mod_cast card_le_card hsub

omit [DecidableEq β] in
/-- Summing the free counts over all tuples `c` gives the number of `(m+1)`-tuples of
codewords with pairwise distinct symbols in coordinate `i`. -/
theorem sum_card_fkFree {m k : ℕ} (w : β → Fin n → Fin k) (i : Fin n) :
    ∑ c : Fin m → β, (fkFree w c i).card =
      ((univ : Finset (Fin (m + 1) → β)).filter
        fun f => Function.Injective ((fun b => w b i) ∘ f)).card := by
  classical
  rw [card_filter, ← (Fin.consEquiv fun _ => β).sum_comp, Fintype.sum_prod_type, sum_comm]
  refine sum_congr rfl fun c _ => ?_
  rw [fkFree, card_filter]
  refine sum_congr rfl fun x _ => ?_
  have hc : (Fin.consEquiv fun _ => β) (x, c) = Fin.cons x c := rfl
  rw [hc]
  refine if_congr ?_ rfl rfl
  rw [Fin.comp_cons, Fin.cons_injective_iff]
  simp only [Set.mem_range, mem_image, mem_univ, true_and, Function.comp_def]
  tauto

/-- **Fredman–Komlós bound, core form.** Let `β` be a finite set of `N` codewords, each a word
`w b` of length `n` over `{0, …, m+1}`, such that any `m + 2` codewords take pairwise distinct
values in some coordinate. Then
`N (N-1) ⋯ (N-m) · log₂ (N - m) ≤ n · (m+2)! · (N / (m+2))^{m+1}`. -/
theorem fredmanKomlos_core {m : ℕ} (w : β → Fin n → Fin (m + 2))
    (H : ∀ S : Finset β, S.card = m + 2 → ∃ i, Set.InjOn (fun b => w b i) S) :
    ((Fintype.card β).descFactorial (m + 1) : ℝ) * Real.logb 2 ((Fintype.card β - m : ℕ) : ℝ) ≤
      n * (m + 2).factorial * ((Fintype.card β : ℝ) / (m + 2 : ℕ)) ^ (m + 1) := by
  classical
  set N := Fintype.card β
  set D : Finset (Fin m → β) := univ.filter Function.Injective with hD
  have hDcard : D.card = N.descFactorial m := by
    rw [hD, ← Fintype.card_subtype, Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding _ _),
      Fintype.card_embedding_eq, Fintype.card_fin]
  set L := ((N - m : ℕ) : ℝ) * Real.logb 2 ((N - m : ℕ) : ℝ)
  have hL0 : ∀ c ∈ D, L ≤ ∑ i, ((fkFree w c i).card : ℝ) := fun c hc =>
    hansel_fkFree w H c (mem_filter.mp hc).2
  have hmass : ∀ i : Fin n,
      ∑ s, ((univ.filter fun b : β => w b i = s).card : ℝ) = N := by
    intro i
    rw [← Nat.cast_sum, ← card_eq_sum_card_fiberwise (fun _ _ => mem_coe.mpr (mem_univ _)),
      card_univ]
  calc ((N.descFactorial (m + 1) : ℕ) : ℝ) * Real.logb 2 ((N - m : ℕ) : ℝ)
      = ∑ _c ∈ D, L := by
        rw [sum_const, hDcard, nsmul_eq_mul, Nat.descFactorial_succ]
        push_cast
        ring
    _ ≤ ∑ c ∈ D, ∑ i, ((fkFree w c i).card : ℝ) := sum_le_sum hL0
    _ ≤ ∑ c : Fin m → β, ∑ i, ((fkFree w c i).card : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _)
          (fun _ _ _ => sum_nonneg fun _ _ => Nat.cast_nonneg _)
    _ = ∑ i, ∑ c : Fin m → β, ((fkFree w c i).card : ℝ) := sum_comm
    _ = ∑ i, injSum (fun s => ((univ.filter fun b : β => w b i = s).card : ℝ)) univ (m + 1) := by
        refine sum_congr rfl fun i _ => ?_
        rw [← Nat.cast_sum, sum_card_fkFree]
        exact card_filter_injective_comp (fun b => w b i) (m + 1)
    _ ≤ ∑ _i : Fin n, ((m + 2).factorial * ((N : ℝ) / (m + 2 : ℕ)) ^ (m + 1) : ℝ) := by
        refine sum_le_sum fun i _ => ?_
        have h := injSum_univ_le (fun s => ((univ.filter fun b : β => w b i = s).card : ℝ))
          (fun _ => Nat.cast_nonneg _) (k := m + 1) (by rw [Fintype.card_fin])
        rw [hmass i] at h
        exact h
    _ = n * (m + 2).factorial * ((N : ℝ) / (m + 2 : ℕ)) ^ (m + 1) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **Fredman–Komlós bound** (1984) for perfect `k`-hash codes, `k ≥ 2`. If `C ⊆ {0,…,k-1}ⁿ`
is a perfect `k`-hash code with `N` words, then
`N (N-1) ⋯ (N-k+2) · k^{k-1} · log₂ (N - k + 2) ≤ n · k! · N^{k-1}`.
(Here `N - (k - 2)` is natural-number subtraction; for `N < k - 1` the left side is `0`.)
As `N → ∞` this gives `log₂ N ≤ (1 + o(1)) · n · k! / k^{k-1}`. -/
theorem IsPerfectHashCode.fredmanKomlos {k n : ℕ} (hk : 2 ≤ k) {C : Finset (Fin n → Fin k)}
    (hC : IsPerfectHashCode k C) :
    (C.card.descFactorial (k - 1) : ℝ) * (k : ℝ) ^ (k - 1) *
        Real.logb 2 ((C.card - (k - 2) : ℕ) : ℝ) ≤
      n * k.factorial * (C.card : ℝ) ^ (k - 1) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have e1 : m + 2 - 1 = m + 1 := by omega
  have e2 : m + 2 - 2 = m := by omega
  rw [e1, e2]
  have H : ∀ S : Finset C, S.card = m + 2 →
      ∃ i, Set.InjOn (fun b : C => (b : Fin n → Fin (m + 2)) i) S := by
    intro S hS
    obtain ⟨i, hi⟩ := hC (S.map (Function.Embedding.subtype _))
      (fun x hx => by
        obtain ⟨y, -, rfl⟩ := mem_map.mp hx
        exact y.2)
      (by rw [card_map, hS])
    refine ⟨i, fun a ha b hb e => Subtype.ext ?_⟩
    exact hi (mem_coe.mpr (mem_map_of_mem _ (mem_coe.mp ha)))
      (mem_coe.mpr (mem_map_of_mem _ (mem_coe.mp hb))) e
  have h := fredmanKomlos_core (β := C) (fun b => (b : Fin n → Fin (m + 2))) H
  rw [Fintype.card_coe] at h
  have hk0 : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by positivity
  have hpow : ((C.card : ℝ) / ((m + 2 : ℕ) : ℝ)) ^ (m + 1) * ((m + 2 : ℕ) : ℝ) ^ (m + 1) =
      (C.card : ℝ) ^ (m + 1) := by
    rw [div_pow]; field_simp
  calc (C.card.descFactorial (m + 1) : ℝ) * ((m + 2 : ℕ) : ℝ) ^ (m + 1) *
        Real.logb 2 ((C.card - m : ℕ) : ℝ)
      = ((C.card.descFactorial (m + 1) : ℝ) * Real.logb 2 ((C.card - m : ℕ) : ℝ)) *
          ((m + 2 : ℕ) : ℝ) ^ (m + 1) := by ring
    _ ≤ (n * (m + 2).factorial * ((C.card : ℝ) / ((m + 2 : ℕ) : ℝ)) ^ (m + 1)) *
          ((m + 2 : ℕ) : ℝ) ^ (m + 1) :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = n * (m + 2).factorial * (C.card : ℝ) ^ (m + 1) := by rw [mul_assoc, hpow]

end FK

end Applied.Coding
