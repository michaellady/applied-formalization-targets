import Mathlib.InformationTheory.Hamming
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-!
# Locally decodable codes

A binary code `C : (Fin k → Bool) → (ι → Bool)` is locally decodable if every message bit can
be recovered, with probability noticeably above `1/2`, by a randomized procedure that reads
only a few positions of a corrupted codeword.

* `LocalDecoder ι k q`: a non-adaptive randomized decoder making `q` queries: a finite
  probability space `Ω`, and for every message index `i` and outcome `ω` a tuple of `q` queried
  positions and a function from the `q` answers to the output bit.
* `LocalDecoder.successProb D y i b`: the probability that `D`, run on the word `y` for the
  message index `i`, outputs `b`.
* `IsLDC C q δ ε`: `C` is a `(q, δ, ε)`-locally decodable code: there is a `q`-query decoder
  which, for every message `x`, every index `i` and every word `y` at Hamming distance at most
  `δ |ι|` from `C x`, outputs `x i` with probability at least `1/2 + ε`.
* `hadamardCode k`: the Hadamard code, `C x a = ⟨a, x⟩ mod 2`, of length `2 ^ k`.
* `isLDC_hadamardCode`: the Hadamard code is a `(2, δ, 1/2 - 2δ)`-locally decodable code for
  every `δ` (the statement has content for `δ < 1/4`).
* `IsLDC.mono`: weakening the parameters `δ` and `ε`; `IsLDC.reindex`: renaming positions.
* `exists_isLDC_two_pow`: two-query locally decodable codes of length `2 ^ k` exist.
-/

open Finset

namespace Applied.Coding

/-- A non-adaptive randomized local decoder for messages of length `k` that reads `q` positions
of a word indexed by `ι`. The randomness is an outcome `ω` of a finite probability space. -/
structure LocalDecoder (ι : Type*) (k q : ℕ) where
  /-- The sample space of the decoder's internal randomness. -/
  Ω : Type
  [fintypeΩ : Fintype Ω]
  /-- The probability of each outcome. -/
  prob : Ω → ℝ
  prob_nonneg : ∀ ω, 0 ≤ prob ω
  prob_sum : ∑ ω, prob ω = 1
  /-- The positions read when decoding the message bit `i` with randomness `ω`. -/
  query : Fin k → Ω → Fin q → ι
  /-- The output bit, as a function of the `q` answers. -/
  out : Fin k → Ω → (Fin q → Bool) → Bool

attribute [instance] LocalDecoder.fintypeΩ

/-- The probability that the decoder `D`, reading the word `y` to decode the message bit `i`,
outputs `b`. -/
def LocalDecoder.successProb {ι : Type*} {k q : ℕ} (D : LocalDecoder ι k q) (y : ι → Bool)
    (i : Fin k) (b : Bool) : ℝ :=
  ∑ ω, if D.out i ω (fun j => y (D.query i ω j)) = b then D.prob ω else 0

/-- `C` is a `(q, δ, ε)`-**locally decodable code**: some non-adaptive `q`-query randomized
decoder recovers every message bit `x i` with probability at least `1/2 + ε` from every word
`y` that differs from the codeword `C x` in at most `δ |ι|` positions. -/
def IsLDC {ι : Type*} [Fintype ι] {k : ℕ} (C : (Fin k → Bool) → (ι → Bool)) (q : ℕ)
    (δ ε : ℝ) : Prop :=
  ∃ D : LocalDecoder ι k q, ∀ (x : Fin k → Bool) (i : Fin k) (y : ι → Bool),
    (hammingDist y (C x) : ℝ) ≤ δ * Fintype.card ι → 1 / 2 + ε ≤ D.successProb y i (x i)

/-- A locally decodable code stays one for a smaller corruption rate and a smaller advantage. -/
theorem IsLDC.mono {ι : Type*} [Fintype ι] {k : ℕ} {C : (Fin k → Bool) → (ι → Bool)} {q : ℕ}
    {δ ε δ' ε' : ℝ} (h : IsLDC C q δ ε) (hδ : δ' ≤ δ) (hε : ε' ≤ ε) : IsLDC C q δ' ε' := by
  obtain ⟨D, hD⟩ := h
  refine ⟨D, fun x i y hy => ?_⟩
  have := hD x i y (hy.trans (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg _)))
  linarith

/-- Local decodability does not depend on how the codeword positions are named. -/
theorem IsLDC.reindex {ι κ : Type*} [Fintype ι] [Fintype κ] {k : ℕ}
    {C : (Fin k → Bool) → (ι → Bool)} {q : ℕ} {δ ε : ℝ} (h : IsLDC C q δ ε) (e : ι ≃ κ) :
    IsLDC (fun x j => C x (e.symm j)) q δ ε := by
  classical
  obtain ⟨D, hD⟩ := h
  refine ⟨{ D with query := fun i ω j => e (D.query i ω j) }, fun x i y hy => ?_⟩
  have hdist : hammingDist (fun a => y (e a)) (C x) = hammingDist y fun j => C x (e.symm j) := by
    unfold hammingDist
    refine Finset.card_bij (fun a _ => e a) (fun a ha => ?_) (fun a _ b _ hab => e.injective hab)
      (fun j hj => ⟨e.symm j, ?_, by simp⟩)
    · simpa using ha
    · simpa using hj
  have := hD x i (fun a => y (e a)) (by rw [hdist, Fintype.card_congr e]; exact hy)
  exact this

/-! ### The Hadamard code -/

/-- The **Hadamard code**: the codeword of `x ∈ {0,1}ᵏ` lists the inner products `⟨a, x⟩ mod 2`
for all `a ∈ {0,1}ᵏ`. -/
def hadamardCode (k : ℕ) (x : Fin k → Bool) (a : Fin k → Bool) : Bool :=
  decide (∑ j, (if a j && x j then (1 : ZMod 2) else 0) = 1)

/-- Flipping the `i`-th bit of the position `a` changes the Hadamard codeword of `x` by `x i`. -/
lemma hadamardCode_update (k : ℕ) (x a : Fin k → Bool) (i : Fin k) :
    hadamardCode k x (Function.update a i (!a i)) = xor (hadamardCode k x a) (x i) := by
  unfold hadamardCode
  have key : ∑ j, (if Function.update a i (!a i) j && x j then (1 : ZMod 2) else 0)
      = (∑ j, if a j && x j then (1 : ZMod 2) else 0) + (if x i then 1 else 0) := by
    rw [← Finset.add_sum_erase _ _ (mem_univ i), ← Finset.add_sum_erase _ _ (mem_univ i)]
    have : ∀ j ∈ univ.erase i,
        (if Function.update a i (!a i) j && x j then (1 : ZMod 2) else 0)
          = if a j && x j then (1 : ZMod 2) else 0 := fun j hj => by
      rw [Function.update_of_ne (ne_of_mem_erase hj)]
    rw [Finset.sum_congr rfl this, Function.update_self]
    generalize (∑ j ∈ univ.erase i, if a j && x j then (1 : ZMod 2) else 0) = s
    cases a i <;> cases x i <;> revert s <;> decide
  rw [key]
  generalize (∑ j, if a j && x j then (1 : ZMod 2) else 0) = s
  cases x i <;> revert s <;> decide

/-- The two-query decoder of the Hadamard code: to decode `x i`, pick `a` uniformly, read the
positions `a` and `a + eᵢ`, and output the sum of the two answers. -/
noncomputable def hadamardDecoder (k : ℕ) : LocalDecoder (Fin k → Bool) k 2 where
  Ω := Fin k → Bool
  prob _ := 1 / 2 ^ k
  prob_nonneg _ := by positivity
  prob_sum := by simp
  query i a j := if j = 0 then a else Function.update a i (!a i)
  out _ _ b := xor (b 0) (b 1)

/-- **The Hadamard code is a two-query locally decodable code**: from any word within relative
distance `δ` of a codeword, each message bit is recovered with probability at least `1 - 2δ`. -/
theorem isLDC_hadamardCode (k : ℕ) (δ : ℝ) : IsLDC (hadamardCode k) 2 δ (1 / 2 - 2 * δ) := by
  classical
  refine ⟨hadamardDecoder k, fun x i y hy => ?_⟩
  set flip : (Fin k → Bool) → (Fin k → Bool) := fun a => Function.update a i (!a i) with hflip
  have hinv : Function.Involutive flip := fun a => by
    funext j
    by_cases hj : j = i
    · subst hj; simp [hflip]
    · simp [hflip, Function.update_of_ne hj]
  -- the positions where `y` is corrupted
  set B : Finset (Fin k → Bool) := univ.filter fun a => y a ≠ hadamardCode k x a with hB
  have hBcard : (B.card : ℝ) ≤ δ * 2 ^ k := by
    have : B.card = hammingDist y (hadamardCode k x) := rfl
    rw [this]; simpa using hy
  -- the outcomes on which the decoder errs
  set bad : Finset (Fin k → Bool) := univ.filter fun a => ¬ xor (y a) (y (flip a)) = x i
    with hbad
  have hsub : bad ⊆ B ∪ B.image flip := by
    intro a ha
    rw [hbad, mem_filter] at ha
    by_contra hnot
    rw [mem_union, not_or, hB, mem_image] at hnot
    have h1 : y a = hadamardCode k x a := by
      by_contra h; exact hnot.1 (mem_filter.mpr ⟨mem_univ _, h⟩)
    have h2 : y (flip a) = hadamardCode k x (flip a) := by
      by_contra h
      exact hnot.2 ⟨flip a, mem_filter.mpr ⟨mem_univ _, h⟩, hinv a⟩
    apply ha.2
    rw [h1, h2, hflip, hadamardCode_update]
    cases hadamardCode k x a <;> cases x i <;> rfl
  have hbadcard : (bad.card : ℝ) ≤ 2 * (δ * 2 ^ k) := by
    have h1 : bad.card ≤ B.card + B.card :=
      (card_le_card hsub).trans ((card_union_le _ _).trans
        (Nat.add_le_add_left card_image_le _))
    have h2 : (bad.card : ℝ) ≤ B.card + B.card := by exact_mod_cast h1
    linarith
  have hsucc : (hadamardDecoder k).successProb y i (x i)
      = ((2 : ℝ) ^ k - bad.card) / 2 ^ k := by
    have hgood : (univ.filter fun a : Fin k → Bool => xor (y a) (y (flip a)) = x i).card
        + bad.card = 2 ^ k := by
      rw [hbad, Finset.card_filter_add_card_filter_not]; simp
    have hgood' : ((univ.filter fun a : Fin k → Bool => xor (y a) (y (flip a)) = x i).card : ℝ)
        = 2 ^ k - bad.card := by
      rw [eq_sub_iff_add_eq]; exact_mod_cast hgood
    rw [← hgood']
    change (∑ a : Fin k → Bool, if xor (y a) (y (flip a)) = x i then (1 / 2 ^ k : ℝ) else 0) = _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hsucc, le_div_iff₀ (by positivity)]
  have : (0 : ℝ) < 2 ^ k := by positivity
  nlinarith

/-- For every `k` there is a two-query locally decodable code of length `2 ^ k`. -/
theorem exists_isLDC_two_pow (k : ℕ) (δ : ℝ) :
    ∃ C : (Fin k → Bool) → (Fin (2 ^ k) → Bool), IsLDC C 2 δ (1 / 2 - 2 * δ) :=
  ⟨_, (isLDC_hadamardCode k δ).reindex (Fintype.equivFinOfCardEq (by simp))⟩

end Applied.Coding
