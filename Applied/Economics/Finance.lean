import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Put–call parity

* `call_sub_put`: the payoff identity `max (S - K) 0 - max (K - S) 0 = S - K`.
* `put_call_parity`: under any pricing measure and discount factor, the price of a European
  call minus the price of the put with the same strike equals the discounted forward value
  `E[D S] - K E[D]`. No model of the asset price is assumed.
-/

open MeasureTheory

namespace Applied.Economics

/-- Payoff identity behind put–call parity. -/
theorem call_sub_put (S K : ℝ) : max (S - K) 0 - max (K - S) 0 = S - K := by
  rcases le_total S K with h | h
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring

/-- **Put–call parity.** `D` is the discount factor and `S` the asset price at expiry, both
random under the pricing measure `Q`. -/
theorem put_call_parity {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) (D S : Ω → ℝ) (K : ℝ)
    (hcall : Integrable (fun ω => D ω * max (S ω - K) 0) Q)
    (hput : Integrable (fun ω => D ω * max (K - S ω) 0) Q)
    (hDS : Integrable (fun ω => D ω * S ω) Q) (hD : Integrable D Q) :
    ∫ ω, D ω * max (S ω - K) 0 ∂Q - ∫ ω, D ω * max (K - S ω) 0 ∂Q
      = ∫ ω, D ω * S ω ∂Q - K * ∫ ω, D ω ∂Q := by
  rw [← integral_sub hcall hput, ← integral_const_mul, ← integral_sub hDS (hD.const_mul K)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  have := call_sub_put (S ω) K
  simp only
  rw [← mul_sub, this]; ring

end Applied.Economics
