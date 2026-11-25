import Applied.InformationTheory.MultiTerminal

/-!
# Open: the capacity region of the three-receiver broadcast channel

- id: info-broadcast-three-receivers
- area: information-theory
- status: open
- source: T. M. Cover, "Broadcast channels", IEEE Trans. Inform. Theory 18 (1972); textbook form A. El Gamal, Y.-H. Kim, "Network Information Theory" (2011), Chapters 5 and 8 (chapter numbers to be confirmed); ProofAtlas Top 500 (Nov 2026), rank 390 (exact wording of the ranked problem to be confirmed, see the review notes)
- used-in: downlink communication from one transmitter to several receivers
- prerequisites: row-stochastic matrices (`Applied/InformationTheory/Channel.lean`); broadcast codes (`Applied/InformationTheory/MultiTerminal.lean`)
- formalized-elsewhere: the three-receiver region was not found in any project checked on 2026-11-25. Two receivers only: FujiHaruka/information-theory (github.com/FujiHaruka/information-theory), `InformationTheory/Shannon/BroadcastChannel/Operational.lean` :: `BCAchievable`, `bcCapacityRegion` (an equivalent notion for two receivers, up to the error criterion and the restriction to nonnegative rates) (clones of 2026-11-25; statements read at source, proofs not re-checked)
- statement-review: unreviewed

Informal statement. A discrete memoryless broadcast channel with three receivers has an input
`x ∈ X` and outputs `y₁, y₂, y₃` with transition probabilities `W(y₁, y₂, y₃ | x)`. A code of
length `n` with `M₁, M₂, M₃` messages encodes a triple of independent messages, one intended
for each receiver, into a word of `Xⁿ`; receiver `j` decodes its own message from its own
output sequence. The error probability is the probability, for uniformly distributed message
triples, that at least one receiver decodes wrongly. A rate triple `(R₁, R₂, R₃)` is
achievable if for every `ε > 0` and all large `n` there is a code with `Mⱼ ≥ exp(n Rⱼ)` and
error probability at most `ε`. The capacity region is the closure of the set of achievable
rate triples with nonnegative coordinates.

The open problem is to give a computable (single-letter) description of
`broadcastCapacityRegion W` for every `W`. Since this is not a proposition, the problem is
recorded as the set `broadcastCapacityRegion W`; no proposition is asserted.

What is proved: error probabilities lie in `[0, 1]` for a row-stochastic `W`
(`errorProb_nonneg`, `errorProb_le_one`); the zero rate triple is achievable and belongs to the
region (`zero_mem_broadcastCapacityRegion`). Nothing else in this file; convexity of the region
(standard) is not proved anywhere in the library.

Partial result elsewhere: an elementary outer bound is proved in
`Targets/InformationTheory/BroadcastOuterBound.lean`. For a row-stochastic `W` with output
alphabets in universe `Type`, every point of the region has `0 ≤ Rⱼ ≤ C(Wⱼ)` (`Wⱼ` the marginal
channel to receiver `j`, `C` the information capacity) and `R₁ + R₂ + R₃ ≤ C(W)`
(`broadcastCapacityRegion_subset`), so the region is bounded
(`isBounded_broadcastCapacityRegion`). This outer bound is not tight in general and does not
determine the region.

Review notes (modelling choices and doubts to check).

* Doubt about the intended problem. The capacity region of the general broadcast channel is
  already open for *two* receivers. We have not confirmed whether the ranked problem means the
  general three-receiver region (as stated here) or a specific three-receiver setting (for
  example degraded message sets, or less-noisy / more-capable orderings, some of which are
  solved). The definition below is the general private-message region.
* Variant: one private message per receiver, *no common message* and no degraded message sets.
* Error criterion: *average* over uniform message triples of the probability that *some*
  receiver errs (as in El Gamal–Kim). The region is believed to be the same under the maximal
  criterion, and depends only on the three marginal channels; neither fact is proved here.
* Units nats; "all sufficiently large `n`"; `Mⱼ ≥ exp (n Rⱼ)`; deterministic encoder and
  decoders; no feedback.
* The region is the topological closure in `ℝ × ℝ × ℝ` of the achievable triples with all
  coordinates `≥ 0`.

Not covered: superposition coding, Marton's inner bound, the UV and Nair–El Gamal outer
bounds; any class for which the region is known.
-/

open Applied.InformationTheory

namespace Targets.InformationTheory

alias broadcastAchievable_zero := Applied.InformationTheory.broadcastAchievable_zero

/-- The open object: the private-message capacity region of the discrete memoryless
three-receiver broadcast channel `W`, in nats per channel use. No single-letter description is
known in general. -/
def broadcastCapacityRegion {X Y₁ Y₂ Y₃ : Type*} [Fintype Y₁] [Fintype Y₂] [Fintype Y₃]
    (W : X → Y₁ × Y₂ × Y₃ → ℝ) : Set (ℝ × ℝ × ℝ) :=
  Applied.InformationTheory.broadcastCapacityRegion W

/-- The zero rate triple belongs to the capacity region. -/
theorem zero_mem_broadcastCapacityRegion {X Y₁ Y₂ Y₃ : Type*} [Fintype Y₁] [Fintype Y₂]
    [Fintype Y₃] [Nonempty X] (W : X → Y₁ × Y₂ × Y₃ → ℝ) :
    (0, 0, 0) ∈ broadcastCapacityRegion W :=
  Applied.InformationTheory.zero_mem_broadcastCapacityRegion W

end Targets.InformationTheory
