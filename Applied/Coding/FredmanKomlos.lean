import Applied.Coding.Hansel
import Applied.Coding.PerfectHash
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.CardEmbedding

/-!
# The Fredman–Komlós bound for perfect `k`-hash codes

## Elementary symmetric polynomial of degree `|A| - 1`

* `esymmTop A m = ∑_{a ∈ A} ∏_{b ∈ A \ {a}} m b` (the elementary symmetric polynomial of degree
  `|A| - 1` in the values `m a`, `a ∈ A`).
* `prod_le_avg_pow`: AM-GM, `∏_{a ∈ A} m a ≤ (S / |A|)^{|A|}` with `S = ∑_{a ∈ A} m a`.
* `esymmTop_le`: the special case of Maclaurin's inequality
  `esymmTop A m ≤ |A| (S / |A|)^{|A| - 1}` for nonnegative `m`.
* `injSum m A j = ∑_{g : Fin j ↪ A} ∏_t m (g t)` (sum over injective maps into `A`), and
  `injSum_eq`: `injSum m A j = j! · esymmTop A m` when `|A| = j + 1`.
* `card_filter_injective_comp`: the number of `j`-tuples of elements of a finite type `β` whose
  images under `φ : β → ι` are pairwise distinct is `injSum (fiber sizes of φ) univ j`.
-/

open Finset

namespace Applied.Coding

section Symmetric

variable {ι : Type*} [DecidableEq ι]

/-- The elementary symmetric polynomial of degree `|A| - 1` in the values `m a`, `a ∈ A`. -/
noncomputable def esymmTop (A : Finset ι) (m : ι → ℝ) : ℝ := ∑ a ∈ A, ∏ b ∈ A.erase a, m b

theorem esymmTop_empty (m : ι → ℝ) : esymmTop ∅ m = 0 := by simp [esymmTop]

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

end Applied.Coding
