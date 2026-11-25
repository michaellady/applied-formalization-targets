import Applied.Privacy.PureDP

/-!
# Randomized response is differentially private

Randomized response (Warner 1965) on a single bit: report the true bit with probability
`e^ε / (1 + e^ε)` and the flipped bit with probability `1 / (1 + e^ε)`.

* `randomizedResponse ε`: the mechanism `Bool → PMF Bool`.
* `randomizedResponse_apply_self`, `randomizedResponse_apply_ne`: its probabilities.
* `randomizedResponse_isPureDP`: it is `ε`-differentially private for `ε ≥ 0`, with respect to
  the relation in which any two inputs are neighbours.
-/

open scoped ENNReal

namespace Applied.Privacy

/-- Probability of reporting the truth, `e^ε / (1 + e^ε)`. -/
noncomputable def rrTruth (ε : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp ε / (1 + Real.exp ε))

/-- Probability of reporting the flipped bit, `1 / (1 + e^ε)`. -/
noncomputable def rrLie (ε : ℝ) : ℝ≥0∞ := ENNReal.ofReal (1 / (1 + Real.exp ε))

lemma rrTruth_add_rrLie (ε : ℝ) : rrTruth ε + rrLie ε = 1 := by
  have h : (0 : ℝ) < 1 + Real.exp ε := by positivity
  rw [rrTruth, rrLie, ← ENNReal.ofReal_add (by positivity) (by positivity), ← add_div,
    add_comm, div_self h.ne', ENNReal.ofReal_one]

/-- **Randomized response**: report the input bit with probability `e^ε / (1 + e^ε)` and its
negation with probability `1 / (1 + e^ε)`. -/
noncomputable def randomizedResponse (ε : ℝ) (b : Bool) : PMF Bool :=
  PMF.ofFintype (fun y => if y = b then rrTruth ε else rrLie ε) (by
    cases b <;> simp [rrTruth_add_rrLie, add_comm (rrLie ε)])

lemma randomizedResponse_apply_self (ε : ℝ) (b : Bool) :
    randomizedResponse ε b b = ENNReal.ofReal (Real.exp ε / (1 + Real.exp ε)) := by
  simp [randomizedResponse, rrTruth]

lemma randomizedResponse_apply_ne (ε : ℝ) {b y : Bool} (h : y ≠ b) :
    randomizedResponse ε b y = ENNReal.ofReal (1 / (1 + Real.exp ε)) := by
  simp [randomizedResponse, rrLie, h]

/-- **Randomized response is `ε`-differentially private** for every `ε ≥ 0`, where any two
input bits count as neighbours. -/
theorem randomizedResponse_isPureDP (ε : ℝ) (hε : 0 ≤ ε) :
    IsPureDP (fun _ _ : Bool => True) ε (randomizedResponse ε) := by
  intro d d' _ y
  have h : (0 : ℝ) < 1 + Real.exp ε := by positivity
  have h1 : (1 : ℝ) ≤ Real.exp ε := Real.one_le_exp hε
  have hval : ∀ b : Bool, randomizedResponse ε b y
      = ENNReal.ofReal (if y = b then Real.exp ε / (1 + Real.exp ε) else 1 / (1 + Real.exp ε)) := by
    intro b
    by_cases hb : y = b
    · subst hb; simp [randomizedResponse_apply_self]
    · simp [randomizedResponse_apply_ne ε hb, hb]
  rw [hval, hval, ← ENNReal.ofReal_mul (Real.exp_pos ε).le]
  apply ENNReal.ofReal_le_ofReal
  have hpos : (0 : ℝ) < Real.exp ε := Real.exp_pos ε
  split_ifs
  · rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ h.le
    nlinarith
  · rw [mul_one_div]
  · rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ h.le
    nlinarith
  · rw [mul_one_div]
    apply div_le_div_of_nonneg_right _ h.le
    linarith

end Applied.Privacy
