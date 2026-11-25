import Mathlib

/-!
# The endgame: what is actually left of the binary problem

`main` carries the pieces that are supposed to be the whole remaining distance
to binary Goldbach:

* `arc-major-floor`      : the major arc contributes at least `c n` (ACCEPTED)
* `minor-bilinear-split` : the minor arc coefficient splits as `w = low + high`
* `small-small-saving`   : the low-low piece is absolutely `o(n)` (ACCEPTED)
* `small-bulk-saving`    : the low-high piece is absolutely `o(n)` (ACCEPTED)
* `bulk-signed-floor`    : the high-high piece has a one-sided floor `-e n` (OPEN)
* `arc-budget-transfer`  : the two arc floors give Goldbach (ACCEPTED)
* `arc-minor-saving`     : the minor arc floor (the stated target)

Nothing in the repository connects them, and `research/gaps.json` records no
dependency edges at all, so the claim that one lemma is left is not checkable there.
This file makes it checkable.

Two results:

1. `bulk_floor_of_minor` / `minor_floor_of_bulk`: given the split and the two
   absolute bounds, the one-sided floor on the whole minor arc and the
   one-sided floor on the high-high piece are *equivalent*. Truncating at
   `k^3 <= n` did not move the difficulty.

2. `goldbach_of_two_floors`: the major floor (already ACCEPTED, `c = 1/144`)
   plus the bulk floor alone already give Goldbach for all large even `n`.
   So `bulk-signed-floor` is not a step towards the theorem; it is the theorem.

No analysis here. The content is `1/8 + 1/4 + 1/8 < 1`, `Re z >= -‖z‖`, and
`simp only [pow_two]` to bridge the `S*S` and `S^2` conventions of two families
of catalogue entries.
-/

namespace PEqualNP.Outside

noncomputable def eW : ℕ → ℝ := fun k => if Nat.Prime k then Real.log (k:ℝ) else 0

noncomputable def eE : ℝ → ℂ := fun x => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)

noncomputable def eS (n : ℕ) (w : ℕ → ℝ) (t : ℝ) : ℂ :=
  Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*eE ((k:ℝ)*t))

noncomputable def eQ (n : ℕ) : ℕ := (Nat.log 2 (n+2))^2

def eArcs (n : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤eQ n ∧ a≤q ∧ Nat.Coprime a q ∧
    |t-(a:ℝ)/(q:ℝ)| ≤ (eQ n:ℝ)/((q:ℝ)*(n:ℝ))}

noncomputable def eLow (n k : ℕ) : ℝ := if k^3≤n then eW k else 0

noncomputable def eHigh (n k : ℕ) : ℝ := eW k - eLow n k

noncomputable def eI (n : ℕ) (a b : ℕ → ℝ) : ℂ :=
  intervalIntegral (fun t => (eArcs n)ᶜ.indicator (fun u => eS n a u*eS n b u*eE (-(n:ℝ)*u)) t)
    (0:ℝ) 1 MeasureTheory.volume

noncomputable def eMinor (n : ℕ) : ℂ :=
  intervalIntegral (fun t => (eArcs n)ᶜ.indicator (fun t => (eS n eW t)^2*eE (-(n:ℝ)*t)) t)
    (0:ℝ) 1 MeasureTheory.volume

noncomputable def eMajor (n : ℕ) : ℂ :=
  intervalIntegral (fun t => (eArcs n).indicator (fun t => (eS n eW t)^2*eE (-(n:ℝ)*t)) t)
    (0:ℝ) 1 MeasureTheory.volume

/-- Glue lemma. Two families of catalogue entries write the same integrand with
different but merely propositionally equal spelling: the `I`-style entries write
`S a u * S b u`, the `minor`/`major`-style entries write `(S w t)^2`. The
composed chain needs this rewrite. -/
theorem eMinor_eq_eI (n : ℕ) : eMinor n = eI n eW eW := by
  simp only [eMinor, eI, pow_two]

/-- `Re z >= -‖z‖`. -/
theorem neg_norm_le_re (z : ℂ) : -(‖z‖) ≤ z.re := by
  have h := Complex.re_le_norm (-z)
  simp only [Complex.neg_re, norm_neg] at h
  linarith

/-- Arithmetic core. `A`, `B`, `C` each carry one `X/8`; they cannot cancel
because they are three separate lower bounds. -/
theorem arith_three {X A B C : ℝ} (hX : 0 ≤ X)
    (hA : -(X/8) ≤ A) (hB : -(X/8) ≤ B) (hC : -(X/8) ≤ C) : -X ≤ A + 2*B + C := by
  linarith

/-- Arithmetic core for the converse. Here `-A` and `-2B` must be bounded
above, so only the upper half of the two norm bounds is used. -/
theorem arith_remainder {X A B C : ℝ} (hX : 0 ≤ X)
    (hA : A ≤ X/8) (hB : B ≤ X/8)
    (hC : -(X/4) ≤ C) : -X ≤ C - A - 2*B := by
  linarith

/-- The split plus the two absolute bounds plus the bulk floor give the signed
floor on the whole minor arc. -/
theorem minor_floor_of_bulk :
    (∀ n : ℕ, eI n eW eW = eI n (eLow n) (eLow n) + 2 * eI n (eLow n) (eHigh n)
        + eI n (eHigh n) (eHigh n)) →
      (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ‖eI n (eLow n) (eLow n)‖ ≤ e*(n:ℝ)) →
      (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ‖eI n (eLow n) (eHigh n)‖ ≤ e*(n:ℝ)) →
      (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
        -(e*(n:ℝ)) ≤ (eI n (eHigh n) (eHigh n)).re) →
      ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e*(n:ℝ)) ≤ (eMinor n).re := by
  intro hsplit hLL hLH hbulk e he
  have he8 : (0:ℝ) < e/8 := by linarith
  obtain ⟨N1, h1⟩ := hLL (e/8) he8
  obtain ⟨N2, h2⟩ := hLH (e/8) he8
  obtain ⟨N3, h3⟩ := hbulk (e/8) he8
  refine ⟨max N1 (max N2 N3), ?_⟩
  intro n hn hne
  have hn1 : N1 ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : N2 ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)
  have hn3 : N3 ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn)
  have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hX : (0:ℝ) ≤ e*(n:ℝ) := mul_nonneg he.le hn0
  have h8 : e/8*(n:ℝ) = (e*(n:ℝ))/8 := by ring
  have hA : -((e*(n:ℝ))/8) ≤ (eI n (eLow n) (eLow n)).re := by
    have hb := h1 n hn1
    have hr := neg_norm_le_re (eI n (eLow n) (eLow n))
    have hb' : ‖eI n (eLow n) (eLow n)‖ ≤ (e*(n:ℝ))/8 := by simpa [h8] using hb
    linarith
  have hB : -((e*(n:ℝ))/8) ≤ (eI n (eLow n) (eHigh n)).re := by
    have hb := h2 n hn2
    have hr := neg_norm_le_re (eI n (eLow n) (eHigh n))
    have hb' : ‖eI n (eLow n) (eHigh n)‖ ≤ (e*(n:ℝ))/8 := by simpa [h8] using hb
    linarith
  have hC : -((e*(n:ℝ))/8) ≤ (eI n (eHigh n) (eHigh n)).re := by
    have hb := h3 n hn3 hne
    have hb' : -(e*(n:ℝ)/8) = -((e*(n:ℝ))/8) := by ring
    linarith
  have hRe : (eI n (eLow n) (eLow n) + 2 * eI n (eLow n) (eHigh n)
      + eI n (eHigh n) (eHigh n)).re
      = (eI n (eLow n) (eLow n)).re + 2 * (eI n (eLow n) (eHigh n)).re
        + (eI n (eHigh n) (eHigh n)).re := by
    simp [Complex.add_re, Complex.mul_re]
  have hmain : -((e*(n:ℝ))) ≤ (eI n eW eW).re := by
    rw [hsplit n, hRe]
    have h := arith_three hX hA hB hC
    linarith
  rwa [eMinor_eq_eI n]

/-- The converse: the whole-arc floor already gives the bulk floor, so the
truncation bought nothing in strength. -/
theorem bulk_floor_of_minor :
    (∀ n : ℕ, eI n eW eW = eI n (eLow n) (eLow n) + 2 * eI n (eLow n) (eHigh n)
        + eI n (eHigh n) (eHigh n)) →
      (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ‖eI n (eLow n) (eLow n)‖ ≤ e*(n:ℝ)) →
      (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ‖eI n (eLow n) (eHigh n)‖ ≤ e*(n:ℝ)) →
      (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e*(n:ℝ)) ≤ (eMinor n).re) →
      ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
        -(e*(n:ℝ)) ≤ (eI n (eHigh n) (eHigh n)).re := by
  intro hsplit hLL hLH hminor e he
  have he4 : (0:ℝ) < e/4 := by linarith
  have he8 : (0:ℝ) < e/8 := by linarith
  obtain ⟨N0, h0⟩ := hminor (e/4) he4
  obtain ⟨N1, h1⟩ := hLL (e/8) he8
  obtain ⟨N2, h2⟩ := hLH (e/8) he8
  refine ⟨max N0 (max N1 N2), ?_⟩
  intro n hn hne
  have hn0' : N0 ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : N1 ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)
  have hn2 : N2 ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn)
  have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hX : (0:ℝ) ≤ e*(n:ℝ) := mul_nonneg he.le hn0
  have h8 : e/8*(n:ℝ) = (e*(n:ℝ))/8 := by ring
  have h4 : e/4*(n:ℝ) = (e*(n:ℝ))/4 := by ring
  have hA2 : (eI n (eLow n) (eLow n)).re ≤ (e*(n:ℝ))/8 := by
    have hb := h1 n hn1
    have hr := Complex.re_le_norm (eI n (eLow n) (eLow n))
    have hb' : ‖eI n (eLow n) (eLow n)‖ ≤ (e*(n:ℝ))/8 := by simpa [h8] using hb
    linarith
  have hB2 : (eI n (eLow n) (eHigh n)).re ≤ (e*(n:ℝ))/8 := by
    have hb := h2 n hn2
    have hr := Complex.re_le_norm (eI n (eLow n) (eHigh n))
    have hb' : ‖eI n (eLow n) (eHigh n)‖ ≤ (e*(n:ℝ))/8 := by simpa [h8] using hb
    linarith
  have hI : -((e*(n:ℝ))/4) ≤ (eI n eW eW).re := by
    have h := h0 n hn0' hne
    have h' : -(e*(n:ℝ)/4) ≤ (eMinor n).re := by simpa [h4] using h
    rw [eMinor_eq_eI n] at h'
    linarith
  have hRe : (eI n (eLow n) (eLow n) + 2 * eI n (eLow n) (eHigh n)
      + eI n (eHigh n) (eHigh n)).re
      = (eI n (eLow n) (eLow n)).re + 2 * (eI n (eLow n) (eHigh n)).re
        + (eI n (eHigh n) (eHigh n)).re := by
    simp [Complex.add_re, Complex.mul_re]
  have hkey : (eI n (eHigh n) (eHigh n)).re
      = (eI n eW eW).re - (eI n (eLow n) (eLow n)).re
        - 2 * (eI n (eLow n) (eHigh n)).re := by
    rw [hsplit n, hRe]
    ring
  rw [hkey]
  have h := arith_remainder hX hA2 hB2 hI
  linarith

/-- **The endgame.** The major-arc floor (ACCEPTED, `c = 1/144`) plus the bulk
floor already give binary Goldbach for every sufficiently large even `n`. -/
theorem goldbach_of_two_floors :
    ((∃ (c : ℝ) (N : ℕ), 0 < c ∧ ∀ n : ℕ, N ≤ n → Even n → c*(n:ℝ) ≤ (eMajor n).re) →
      (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e*(n:ℝ)) ≤ (eMinor n).re) →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
        ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q = n) →
    (∃ (c : ℝ) (N : ℕ), 0 < c ∧ ∀ n : ℕ, N ≤ n → Even n → c*(n:ℝ) ≤ (eMajor n).re) →
    (∀ n : ℕ, eI n eW eW = eI n (eLow n) (eLow n) + 2 * eI n (eLow n) (eHigh n)
        + eI n (eHigh n) (eHigh n)) →
    (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ‖eI n (eLow n) (eLow n)‖ ≤ e*(n:ℝ)) →
    (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ‖eI n (eLow n) (eHigh n)‖ ≤ e*(n:ℝ)) →
    (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
        -(e*(n:ℝ)) ≤ (eI n (eHigh n) (eHigh n)).re) →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q = n :=
  fun htransfer hmajor hsplit hLL hLH hbulk =>
    htransfer hmajor (minor_floor_of_bulk hsplit hLL hLH hbulk)

/-- **The endgame, in catalogue form.**

The six hypotheses are, verbatim, the conclusions of six published entries:

* `arc-budget-transfer` (ACCEPTED)
* `arc-major-floor` (ACCEPTED, `c = 1/144`)
* `minor-bilinear-split` (ACCEPTED)
* `small-small-saving` (ACCEPTED)
* `small-bulk-saving` (ACCEPTED)
* `bulk-signed-floor` (open)

The conclusion is binary Goldbach for all sufficiently large even `n`. So the
five accepted entries plus the one open entry already give the theorem: the
project is not several lemmas away, it is one lemma away and that lemma is the
theorem.
-/
theorem L_goldbach_endgame :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let minor := fun n : ℕ => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun t => (S n w t)^2*E (-(n:ℝ)*t)) t) (0:ℝ) 1 MeasureTheory.volume; let major := fun n : ℕ => intervalIntegral (fun t => (arcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; (((∃ (c : ℝ) (N : ℕ), 0<c ∧ ∀ n : ℕ, N≤n → Even n → c*(n:ℝ) ≤ (major n).re) → (∀ e : ℝ, 0<e → ∃ N : ℕ, ∀ n : ℕ, N≤n → Even n → -(e*(n:ℝ)) ≤ (minor n).re) → ∃ N : ℕ, ∀ n : ℕ, N≤n → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n)) → ((∃ (c : ℝ) (N : ℕ), 0<c ∧ ∀ n : ℕ, N≤n → Even n → c*(n:ℝ) ≤ (major n).re)) → (∀ n:ℕ, I n w w=I n (low n) (low n)+2*I n (low n) (high n)+I n (high n) (high n)) → (∀ e:ℝ, 0<e → ∃ N:ℕ, ∀ n:ℕ, N≤n → ‖I n (low n) (low n)‖≤e*(n:ℝ)) → (∀ e:ℝ, 0<e → ∃ N:ℕ, ∀ n:ℕ, N≤n → ‖I n (low n) (high n)‖≤e*(n:ℝ)) → (∀ e:ℝ, 0<e → ∃ N:ℕ, ∀ n:ℕ, N≤n → Even n → -(e*(n:ℝ))≤(I n (high n) (high n)).re) → ∃ N:ℕ, ∀ n:ℕ, N≤n → Even n → ∃ p q:ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n := by
  exact goldbach_of_two_floors

end PEqualNP.Outside
