import Applied.InformationTheory.MultiTerminal

/-!
# Open: the capacity of the general relay channel

- id: info-relay-channel-capacity
- area: information-theory
- status: open
- source: E. C. van der Meulen, "Three-terminal communication channels", Adv. Appl. Probab. 3 (1971); T. M. Cover, A. El Gamal, "Capacity theorems for the relay channel", IEEE Trans. Inform. Theory 25 (1979); textbook form A. El Gamal, Y.-H. Kim, "Network Information Theory" (2011), Chapter 16 (chapter number to be confirmed); ProofAtlas Top 500 (Nov 2026), rank 155
- used-in: cooperative and multi-hop wireless communication
- prerequisites: row-stochastic matrices (`Applied/InformationTheory/Channel.lean`); relay codes (`Applied/InformationTheory/MultiTerminal.lean`)
- formalized-elsewhere: to be confirmed
- statement-review: unreviewed

Informal statement. A discrete memoryless relay channel has a sender input `x ∈ X`, a relay
input `x₁ ∈ X₁`, a receiver output `y ∈ Y` and a relay output `y₁ ∈ Y₁`, with transition
probabilities `W(y, y₁ | x, x₁)`. An `(n, M)` code consists of an encoder
`{0, …, M-1} → Xⁿ`, relay functions giving the relay's input at time `t` as a function of its
outputs `y₁` at times strictly before `t`, and a decoder `Yⁿ → {0, …, M-1}`. The channel is
used `n` times, independently given the inputs. A rate `R` is achievable if for every `ε > 0`
and all large `n` there is an `(n, M)` code with `M ≥ exp(n R)` and maximal error probability
at most `ε`; the capacity `relayCapacity W` is the supremum of the achievable rates.

The open problem is to give a computable (single-letter) formula for `relayCapacity W` for
every relay channel `W`. It is known for special classes (degraded, reversely degraded,
semi-deterministic, …) and bounded in general by the cut-set bound and by the
decode-forward and compress-forward lower bounds. Since "find a formula" is not a
proposition, the problem is recorded as the quantity `relayCapacity W`; no proposition is
asserted.

What is proved: for a row-stochastic `W` (and nonempty alphabets) the joint law of the output
sequences under any relay code sums to `1` (`sum_outProb`); error probabilities lie in `[0, 1]`
(`errorProb_nonneg`, `errorProb_le_one`); rate `0` is achievable (`relayAchievable_zero`) and
every achievable rate is at most `log |X|` (`relayAchievable_le_log_card`), so
`0 ≤ relayCapacity W ≤ log |X|` (`relayCapacity_bounds`) and the supremum is that of a bounded
nonempty set.

Review notes (modelling choices to check).

* Causality: the relay function at time `t` is a function `(Fin n → Y₁) → X₁` together with a
  proof that it depends only on the coordinates `j < t` (strictly causal, as in Cover–El
  Gamal; "relay-without-delay" variants are different). The relay has no message of its own
  and no private randomness; encoder, relay and decoder are deterministic.
* The joint probability of `(yᵗ, y₁ᵗ)_t` is `∏ₜ W(yₜ, y₁ₜ | xₜ(m), x₁ₜ(y₁ before t))`.
* Error criterion: *maximal* error probability over messages. Cover–El Gamal and El Gamal–Kim
  use the average error probability; since there is a single message set, the standard
  expurgation argument should give the same capacity, but this is not proved here.
* Units nats; "all sufficiently large `n`"; `M ≥ exp (n R)`; capacity is `sSup` of the set of
  achievable rates.
* Finite alphabets only (no Gaussian relay channel); no feedback to the sender.

Not covered: the cut-set bound; decode-forward and compress-forward; any special class for
which the capacity is known.
-/

open Applied.InformationTheory

namespace Targets.InformationTheory

alias sum_outProb := Applied.InformationTheory.RelayCode.sum_outProb

alias relayAchievable_zero := Applied.InformationTheory.relayAchievable_zero

alias relayAchievable_le_log_card := Applied.InformationTheory.RelayAchievable.le_log_card

/-- The open quantity: the capacity of the discrete memoryless relay channel `W`, in nats per
channel use. No single-letter formula is known in general. -/
noncomputable def relayCapacity {X X₁ Y Y₁ : Type*} [Fintype Y] [Fintype Y₁]
    (W : X × X₁ → Y × Y₁ → ℝ) : ℝ :=
  Applied.InformationTheory.relayCapacity W

/-- Trivial bounds: `0 ≤ C ≤ log |X|` for every relay channel. -/
theorem relayCapacity_bounds {X X₁ Y Y₁ : Type*} [Fintype X] [Fintype Y] [Fintype Y₁]
    [Nonempty X] [Nonempty X₁] [Nonempty Y] [Nonempty Y₁] {W : X × X₁ → Y × Y₁ → ℝ}
    (hW : IsChannel W) :
    0 ≤ relayCapacity W ∧ relayCapacity W ≤ Real.log (Fintype.card X) :=
  ⟨relayCapacity_nonneg W, relayCapacity_le_log_card hW⟩

end Targets.InformationTheory
