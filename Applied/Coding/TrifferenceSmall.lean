import Applied.Coding.Trifference

/-!
# Trifferent codes: small cases and elementary constructions

Write `T(n)` for the largest size of a trifferent code in `{0,1,2}ⁿ`.

* `isTrifferent_of_card_le_two`: a code with at most two words is trifferent.
* `exists_isTrifferent_card_three`: for `n ≥ 1` the three constant words form a trifferent code.
* `IsTrifferent.padZero`, `exists_isTrifferent_succ`: `T(n) ≤ T(n + 1)`.
* Exact values `T(1) = 3`, `T(2) = 4`, `T(3) = 6`, `T(4) = 9`: the upper bounds
  (`IsTrifferent.card_le_three`, `card_le_four`, `card_le_six`, `card_le_nine`) come from the
  integer form of Körner's shortening step, and the matching codes
  (`exists_isTrifferent_one`, …, `exists_isTrifferent_four`) are the tetracode
  `{(a, b, a + b, a + 2b)}` over `𝔽₃` and two shortenings of it.
-/

open Finset

namespace Applied.Coding

/-- A code with at most two words is trifferent (there are no three distinct codewords). -/
theorem isTrifferent_of_card_le_two {n : ℕ} {C : Finset (Fin n → Fin 3)} (hC : C.card ≤ 2) :
    IsTrifferent C := by
  classical
  intro x hx y hy z hz hxy hyz hxz
  exfalso
  have hsub : ({x, y, z} : Finset (Fin n → Fin 3)) ⊆ C := by
    intro w hw
    simp only [mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> assumption
  have h3 : ({x, y, z} : Finset (Fin n → Fin 3)).card = 3 := by
    rw [card_insert_of_notMem (by simp [hxy, hxz]), card_insert_of_notMem (by simp [hyz]),
      card_singleton]
  have := card_le_card hsub
  omega

/-- For `n ≥ 1` the three constant words form a trifferent code of size 3. -/
theorem exists_isTrifferent_card_three (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : Finset (Fin n → Fin 3), IsTrifferent C ∧ C.card = 3 := by
  classical
  have hinj : Function.Injective (fun (s : Fin 3) (_ : Fin n) => s) :=
    fun a b h => congrFun h ⟨0, hn⟩
  refine ⟨univ.image fun (s : Fin 3) (_ : Fin n) => s, ?_, ?_⟩
  · intro x hx y hy z hz hxy hyz hxz
    obtain ⟨a, -, rfl⟩ := mem_image.mp hx
    obtain ⟨b, -, rfl⟩ := mem_image.mp hy
    obtain ⟨c, -, rfl⟩ := mem_image.mp hz
    exact ⟨⟨0, hn⟩, fun h => hxy (by simp only [h]), fun h => hyz (by simp only [h]),
      fun h => hxz (by simp only [h])⟩
  · rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fin]

/-- Prepending a constant symbol preserves trifference. -/
theorem IsTrifferent.padZero {n : ℕ} {C : Finset (Fin n → Fin 3)} (hC : IsTrifferent C) :
    IsTrifferent (C.map ⟨Fin.cons (0 : Fin 3), Fin.cons_right_injective _⟩) := by
  intro x hx y hy z hz hxy hyz hxz
  obtain ⟨a, ha, rfl⟩ := mem_map.mp hx
  obtain ⟨b, hb, rfl⟩ := mem_map.mp hy
  obtain ⟨c, hc, rfl⟩ := mem_map.mp hz
  obtain ⟨i, h1, h2, h3⟩ := hC a ha b hb c hc (fun h => hxy (by rw [h])) (fun h => hyz (by rw [h]))
    (fun h => hxz (by rw [h]))
  exact ⟨i.succ, by simpa using h1, by simpa using h2, by simpa using h3⟩

/-- A trifferent code of length `n` gives one of the same size and length `n + 1`. -/
theorem exists_isTrifferent_succ {n : ℕ} {C : Finset (Fin n → Fin 3)} (hC : IsTrifferent C) :
    ∃ C' : Finset (Fin (n + 1) → Fin 3), IsTrifferent C' ∧ C'.card = C.card :=
  ⟨_, hC.padZero, card_map _⟩

/-! ### Upper bounds for lengths 1 to 4 -/

/-- `T(1) ≤ 3`. -/
theorem IsTrifferent.card_le_three {C : Finset (Fin 1 → Fin 3)} (_hC : IsTrifferent C) :
    C.card ≤ 3 := by
  have h := Finset.card_le_univ C
  rwa [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h

/-- `T(2) ≤ 4`. -/
theorem IsTrifferent.card_le_four {C : Finset (Fin 2 → Fin 3)} (hC : IsTrifferent C) :
    C.card ≤ 4 := by
  rcases hC.exists_shorter with h | ⟨C', hC', h⟩
  · omega
  · have := hC'.card_le_three; omega

/-- `T(3) ≤ 6`. -/
theorem IsTrifferent.card_le_six {C : Finset (Fin 3 → Fin 3)} (hC : IsTrifferent C) :
    C.card ≤ 6 := by
  rcases hC.exists_shorter with h | ⟨C', hC', h⟩
  · omega
  · have := hC'.card_le_four; omega

/-- `T(4) ≤ 9`. -/
theorem IsTrifferent.card_le_nine {C : Finset (Fin 4 → Fin 3)} (hC : IsTrifferent C) :
    C.card ≤ 9 := by
  rcases hC.exists_shorter with h | ⟨C', hC', h⟩
  · omega
  · have := hC'.card_le_six; omega

/-! ### Matching codes -/

/-- `T(1) ≥ 3`: all three words of length 1. -/
theorem exists_isTrifferent_one : ∃ C : Finset (Fin 1 → Fin 3), IsTrifferent C ∧ C.card = 3 :=
  exists_isTrifferent_card_three 1 le_rfl

/-- The tetracode `(a, b) ↦ (a, b, a + b, a + 2b)` over `𝔽₃`. -/
def tetra (v : Fin 3 × Fin 3) : Fin 4 → Fin 3 := ![v.1, v.2, v.1 + v.2, v.1 + 2 * v.2]

/-- The tetracode shortened once: `(a, b) ↦ (b, a + b, a + 2b)` for `a ≠ 0`. -/
def tetra3 (v : Fin 3 × Fin 3) : Fin 3 → Fin 3 := ![v.2, v.1 + v.2, v.1 + 2 * v.2]

/-- The tetracode shortened twice: `(a, b) ↦ (a + b, a + 2b)` for `a ≠ 0`, `b ≠ 0`. -/
def tetra2 (v : Fin 3 × Fin 3) : Fin 2 → Fin 3 := ![v.1 + v.2, v.1 + 2 * v.2]

private lemma tetra_key : ∀ u v w : Fin 3 × Fin 3, u ≠ v → v ≠ w → u ≠ w →
    ∃ i, tetra u i ≠ tetra v i ∧ tetra v i ≠ tetra w i ∧ tetra u i ≠ tetra w i := by
  decide

private lemma tetra3_key : ∀ u v w : Fin 3 × Fin 3, u.1 ≠ 0 → v.1 ≠ 0 → w.1 ≠ 0 →
    u ≠ v → v ≠ w → u ≠ w →
    ∃ i, tetra3 u i ≠ tetra3 v i ∧ tetra3 v i ≠ tetra3 w i ∧ tetra3 u i ≠ tetra3 w i := by
  decide

private lemma tetra2_key : ∀ u v w : Fin 3 × Fin 3, u.1 ≠ 0 → v.1 ≠ 0 → w.1 ≠ 0 →
    u.2 ≠ 0 → v.2 ≠ 0 → w.2 ≠ 0 → u ≠ v → v ≠ w → u ≠ w →
    ∃ i, tetra2 u i ≠ tetra2 v i ∧ tetra2 v i ≠ tetra2 w i ∧ tetra2 u i ≠ tetra2 w i := by
  decide

private lemma tetra_inj : ∀ u v : Fin 3 × Fin 3, tetra u = tetra v → u = v := by decide
private lemma tetra3_inj : ∀ u v : Fin 3 × Fin 3, tetra3 u = tetra3 v → u = v := by decide
private lemma tetra2_inj : ∀ u v : Fin 3 × Fin 3, tetra2 u = tetra2 v → u = v := by decide

/-- `T(4) ≥ 9`: the tetracode is a trifferent code of length 4 with 9 words. -/
theorem exists_isTrifferent_four : ∃ C : Finset (Fin 4 → Fin 3), IsTrifferent C ∧ C.card = 9 := by
  classical
  refine ⟨univ.image tetra, ?_, ?_⟩
  · intro x hx y hy z hz hxy hyz hxz
    obtain ⟨u, -, rfl⟩ := mem_image.mp hx
    obtain ⟨v, -, rfl⟩ := mem_image.mp hy
    obtain ⟨w, -, rfl⟩ := mem_image.mp hz
    exact tetra_key u v w (fun h => hxy (by rw [h])) (fun h => hyz (by rw [h]))
      (fun h => hxz (by rw [h]))
  · rw [card_image_of_injective _ fun u v => tetra_inj u v]; rfl

/-- `T(3) ≥ 6`. -/
theorem exists_isTrifferent_three : ∃ C : Finset (Fin 3 → Fin 3), IsTrifferent C ∧ C.card = 6 := by
  classical
  refine ⟨(univ.filter fun v : Fin 3 × Fin 3 => v.1 ≠ 0).image tetra3, ?_, ?_⟩
  · intro x hx y hy z hz hxy hyz hxz
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hy
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
    exact tetra3_key u v w (mem_filter.mp hu).2 (mem_filter.mp hv).2 (mem_filter.mp hw).2
      (fun h => hxy (by rw [h])) (fun h => hyz (by rw [h])) (fun h => hxz (by rw [h]))
  · rw [card_image_of_injective _ fun u v => tetra3_inj u v]; rfl

/-- `T(2) ≥ 4`. -/
theorem exists_isTrifferent_two : ∃ C : Finset (Fin 2 → Fin 3), IsTrifferent C ∧ C.card = 4 := by
  classical
  refine ⟨(univ.filter fun v : Fin 3 × Fin 3 => v.1 ≠ 0 ∧ v.2 ≠ 0).image tetra2, ?_, ?_⟩
  · intro x hx y hy z hz hxy hyz hxz
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hy
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
    have hu := (mem_filter.mp hu).2
    have hv := (mem_filter.mp hv).2
    have hw := (mem_filter.mp hw).2
    exact tetra2_key u v w hu.1 hv.1 hw.1 hu.2 hv.2 hw.2
      (fun h => hxy (by rw [h])) (fun h => hyz (by rw [h])) (fun h => hxz (by rw [h]))
  · rw [card_image_of_injective _ fun u v => tetra2_inj u v]; rfl

end Applied.Coding
