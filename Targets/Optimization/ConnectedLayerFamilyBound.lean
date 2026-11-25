import Applied.Optimization.ConnectedLayerFamily

/-!
# Connected layer families have quasi-polynomial length

- id: opt-connected-layer-family-quasipoly
- area: optimization
- status: formalized
- source: F. Eisenbrand, N. Hähnle, A. Razborov, T. Rothvoß, "Diameter of polyhedra: limits of abstraction", Math. Oper. Res. 35(4) (2010) 786–794 (the abstraction and the bound `f(d, n) ≤ n ^ (1 + log₂ d)`; theorem numbers to be confirmed); the recursion is the argument of G. Kalai, D. J. Kleitman, "A quasi-polynomial bound for the diameter of graphs of polyhedra", Bull. Amer. Math. Soc. 26 (1992) 315–316, transferred to the abstract setting
- used-in: the polynomial Hirsch conjecture (`Targets/Optimization/PolynomialHirsch.lean`): the diameter of a simple polytope is bounded in terms of this abstract quantity (EHRR; NOT formalized here)
- prerequisites: `Finset`, `Nat.findGreatest`, `Nat.log`, `Real.logb`, `Real.rpow` (Mathlib)
- formalized-elsewhere: not checked
- statement-review: unreviewed

Informal statement. Let `α` be a type with decidable equality, `U` a finite subset of `α`,
`d t : ℕ` and `F 0, F 1, …` families of finite subsets of `α`. Say
(`IsConnectedLayerFamily d U F t`) that `F 0, …, F (t - 1)` is a connected layer family if
(i) each `F i`, `i < t`, is nonempty; (ii) `F i` and `F j` are disjoint for `i ≠ j < t`;
(iii) every set in every `F i`, `i < t`, is a subset of `U` with exactly `d` elements; and
(iv) for all `i < j < k < t`, `S ∈ F i` and `T ∈ F k` there is `R ∈ F j` with `S ∩ T ⊆ R`.
The layers `F i` with `i ≥ t` play no role.

1. (`connected_layer_family_length_le`) If `1 ≤ d` and `U` has at most `n` elements, then
   `t ≤ n * (d + 1) ^ ⌊log₂ n⌋` (`Nat.log 2 n`, with `Nat.log 2 0 = 0`).
2. (`connected_layer_family_length_le_rpow`) Under the same hypotheses,
   `t ≤ n ^ (1 + log₂ (d + 1))` as real numbers (`Real.logb 2`). For `n = 0` both sides are
   `0` (the exponent is positive, so `0 ^ … = 0`); this is not vacuous because then `t = 0`.
3. (`connected_layer_family_recursion`) The recursion behind 1: let `g` bound the length of
   every connected layer family of `d`-sets on a ground set of at most `m` elements, and `h`
   the length of every family of `(d - 1)`-sets on at most `n - 1` elements (any type `α`
   fixed, any layers). If `U.card ≤ n ≤ 2 m + 1`, then `t ≤ 2 g + h`. Here `d - 1` and
   `n - 1` are truncated subtraction; for `d = 0` the hypothesis on `h` is about `0`-sets
   again and the conclusion still holds (but item 4 is sharper).
4. (`connected_layer_family_length_le_one_of_d_zero`) If `d = 0` then `t ≤ 1`.
5. (`connected_layer_family_length_eq_zero`) If `1 ≤ d` and `U` is empty then `t = 0`.
6. (`connected_layer_family_window`) The hypotheses are satisfiable with length `n - d + 1`:
   for `1 ≤ d ≤ n`, the layers `F i = {{i, i + 1, …, i + d - 1}}` (`Finset.Ico i (i + d)`)
   form a connected layer family on `U = {0, …, n - 1}` of length `n - d + 1`. So the largest
   length is at least `n - d + 1` (a Hirsch-type lower bound) whenever `1 ≤ d ≤ n`.

Proof idea of 1 and 3 (Kalai–Kleitman). Take the longest prefix of layers using at most
`⌊n/2⌋` elements and the longest suffix doing the same; each has length at most `g` by
restricting the ground set. If they do not cover all layers, the prefix extended by one layer
and the suffix extended by one layer each use more than `⌊n/2⌋` elements, so they share an
element `x`. By (iv), the layers between a set containing `x` in the first and a set containing
`x` in the second all contain a set containing `x`; removing `x` gives a connected layer family
of `(d - 1)`-sets on `U \ {x}`, of length at most `h`. Induction on `d` and strong induction on
`n` with the bound `n (d + 1) ^ ⌊log₂ n⌋` closes the recursion.

Differences from the textbook statement. EHRR define `f(d, n)` as the largest length of such a
family of `d`-subsets of `[n] = {1, …, n}` and prove `f(d, n) ≤ n ^ (1 + log₂ d)`; our bound
`n ^ (1 + log₂ (d + 1))` (equivalently `n (d + 1) ^ ⌊log₂ n⌋`) is slightly weaker (it has
`d + 1` in place of `d`) but of the same quasi-polynomial form `n ^ O(log d)`. We do not
define the maximum `f(d, n)` as a number; we bound the length of every family. The ground set
is an arbitrary finite set of size at most `n` in an arbitrary type, which covers `[n]`. The
exact form of EHRR's definition (in particular whether layers must be disjoint and nonempty,
and indexing conventions) is reproduced from memory and is to be confirmed. Both conditions
matter: disjointness gives item 4 and is inherited by the link families in the proof (without
it, repeating one layer gives arbitrarily long families; an easy remark, not formalized), and
nonemptiness is used in the link step and in item 5.

Not covered. The connection to polytopes: EHRR show that for a simple `d`-polytope with `n`
facets the layers of a breadth-first search from a vertex, each vertex identified with the set
of `d` facets containing it, form such a family, so the diameter is less than `f(d, n)`; this
needs faces, facets and simple polytopes, which the library's polytope graph
(`Applied/Optimization/PolytopeGraph.lean`, defined through extreme points and extreme
segments) does not provide, so NO statement about polytope diameters follows from this file.
Also not covered: EHRR's lower bound `f(d, n) = Ω(n² / log n)` for suitable `d` (so no linear
bound holds in the abstract setting); Larman's bound `2 ^ (d - 1) n`; later improvements
(Todd; Sukegawa; details to be confirmed). Whether `f(d, n)` is bounded by a polynomial in
`n` and `d` is, to our knowledge, open; it is not stated here.
-/

namespace Targets.Optimization

open Applied.Optimization

alias connected_layer_family_length_le := Applied.Optimization.IsConnectedLayerFamily.length_le

alias connected_layer_family_length_le_rpow :=
  Applied.Optimization.IsConnectedLayerFamily.length_le_rpow

alias connected_layer_family_recursion :=
  Applied.Optimization.IsConnectedLayerFamily.length_le_two_mul_add

alias connected_layer_family_length_le_one_of_d_zero :=
  Applied.Optimization.IsConnectedLayerFamily.length_le_one_of_card_zero

alias connected_layer_family_length_eq_zero :=
  Applied.Optimization.IsConnectedLayerFamily.length_eq_zero_of_card_eq_zero

alias connected_layer_family_window := Applied.Optimization.isConnectedLayerFamily_window

end Targets.Optimization
