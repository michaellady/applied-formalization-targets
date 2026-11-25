import Applied.SignalProcessing.DiscreteSampling

/-!
# Discrete sampling theorem on `ZMod N`

- id: sp-discrete-sampling-theorem
- area: signal-processing
- status: formalized
- source: finite analogue of the Nyquist–Shannon sampling theorem (C. Shannon, "Communication in the presence of noise", Proc. IRE 37 (1949)); a reference stating exactly this finite form is to be confirmed
- used-in: decimation and interpolation of band-limited discrete signals, multirate signal processing, OFDM
- prerequisites: Mathlib's discrete Fourier transform `ZMod.dft` and its inverse; a polynomial of degree `< K` with `K` distinct roots is zero
- formalized-elsewhere: none found in the Lean projects surveyed (atlas-lean, cslib-frontier, optlib, econcslib, fltk, lean-cksd, sampcert, tcslib, lmlexplore and others; prior-art cross-check, Nov 2026)
- statement-review: unreviewed

Informal statement. Let `N = K · M` with `N ≥ 1`, and let `a` be any residue mod `N`. Let
`x, y : ZMod N → ℂ` be two signals whose discrete Fourier transforms
`𝓕 x k = ∑_j exp(-2πi jk/N) x j` vanish at every frequency `k` that is not one of the `K`
consecutive residues `a, a + 1, …, a + K - 1` (mod `N`). If `x (jM) = y (jM)` for
`j = 0, …, K - 1`, then `x = y`. Equivalently (`eq_zero_of_bandLimited_of_samples`): a signal
with spectrum in such a block whose `K` equally spaced samples vanish is zero.

Not covered: an explicit reconstruction (interpolation) formula, sampling grids with a
nonzero offset, spectra supported on sets other than a block of consecutive frequencies,
sharpness (that fewer samples do not suffice), and the continuous-time
Nyquist–Shannon theorem itself.
-/

namespace Targets.SignalProcessing

alias eq_zero_of_bandLimited_of_samples :=
  Applied.SignalProcessing.eq_zero_of_bandLimited_of_samples
alias eq_of_bandLimited_of_samples := Applied.SignalProcessing.eq_of_bandLimited_of_samples

end Targets.SignalProcessing
