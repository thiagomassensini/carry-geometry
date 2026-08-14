import CarryGeometry.Normalization
import Mathlib.Data.Fin.Embedding

/-!
# Finite positional windows as exact equivalences

The normalization layer proves that evaluation is bijective from admissible
base-`b` strings of length `k` to the residual interval `[0, b ^ k)`.  This
module packages that theorem as an `Equiv` with `Fin (b ^ k)` and uses it to
define exact coordinate changes between windows of equal cardinality.

No equality of cardinalities is manufactured: a finite camera change is an
equivalence only when the two place values are equal.

When the source window has no more states than the target, the same residue
coordinate gives a canonical value-preserving embedding.  At strict
inequality this map is proved not to be surjective.
-/

namespace CarryGeometry

noncomputable section

/-- The type of admissible strings of exactly `k` base-`b` digits. -/
abbrev DigitWindow (b : ℕ) (hb : 1 < b) (k : ℕ) :=
  {digits : List ℕ // digits ∈ admissibleDigitStrings b hb k}

/-- The subtype `[0, N)` is canonically equivalent to `Fin N`. -/
def rangeSubtypeEquivFin (N : ℕ) :
    {n : ℕ // n ∈ Finset.range N} ≃ Fin N where
  toFun n := ⟨n.1, by simpa only [Finset.mem_range] using n.2⟩
  invFun n := ⟨n.1, by simpa only [Finset.mem_range] using n.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/--
Evaluation is the exact equivalence between a finite digit window and its
residual coordinate space.
-/
def digitWindowResidueEquiv
    (b : ℕ) (hb : 1 < b) (k : ℕ) :
    DigitWindow b hb k ≃ Fin (placeValue b k) :=
  (Set.BijOn.equiv (rawExpansionValue b)
      (eval_bijects_admissibleDigitStrings_and_residues b hb k)).trans
    (rangeSubtypeEquivFin (placeValue b k))

/-- The residual coordinate of a digit window is its positional value. -/
@[simp] theorem digitWindowResidueEquiv_apply_val
    (b : ℕ) (hb : 1 < b) (k : ℕ) (digits : DigitWindow b hb k) :
    (digitWindowResidueEquiv b hb k digits).val =
      rawExpansionValue b digits.1 := by
  rfl

/--
Exact change of finite positional coordinates.

The hypothesis is equality of the two window cardinalities.  Without it, the
finite state spaces cannot be equivalent in general.
-/
def matchedCameraEquiv
    (b c : ℕ) (hb : 1 < b) (hc : 1 < c) (k l : ℕ)
    (hcard : placeValue b k = placeValue c l) :
    DigitWindow b hb k ≃ DigitWindow c hc l :=
  (digitWindowResidueEquiv b hb k).trans
    ((finCongr hcard).trans (digitWindowResidueEquiv c hc l).symm)

/-- Exact camera change preserves the represented natural number. -/
@[simp] theorem matchedCameraEquiv_preserves_value
    (b c : ℕ) (hb : 1 < b) (hc : 1 < c) (k l : ℕ)
    (hcard : placeValue b k = placeValue c l)
    (digits : DigitWindow b hb k) :
    rawExpansionValue c (matchedCameraEquiv b c hb hc k l hcard digits).1 =
      rawExpansionValue b digits.1 := by
  rw [← digitWindowResidueEquiv_apply_val b hb k digits,
    ← digitWindowResidueEquiv_apply_val c hc l
      (matchedCameraEquiv b c hb hc k l hcard digits)]
  simp [matchedCameraEquiv]

/-- Reversing a matched camera change gives the change in the opposite direction. -/
theorem matchedCameraEquiv_symm
    (b c : ℕ) (hb : 1 < b) (hc : 1 < c) (k l : ℕ)
    (hcard : placeValue b k = placeValue c l) :
    (matchedCameraEquiv b c hb hc k l hcard).symm =
      matchedCameraEquiv c b hc hb l k hcard.symm := by
  apply Equiv.ext
  intro digits
  apply (digitWindowResidueEquiv b hb k).injective
  apply Fin.ext
  simp [matchedCameraEquiv]

/-- Matched camera changes compose coherently through an intermediate camera. -/
theorem matchedCameraEquiv_trans
    (b c d : ℕ) (hb : 1 < b) (hc : 1 < c) (hd : 1 < d)
    (k l m : ℕ)
    (hbc : placeValue b k = placeValue c l)
    (hcd : placeValue c l = placeValue d m) :
    (matchedCameraEquiv b c hb hc k l hbc).trans
        (matchedCameraEquiv c d hc hd l m hcd) =
      matchedCameraEquiv b d hb hd k m (hbc.trans hcd) := by
  apply Equiv.ext
  intro digits
  apply (digitWindowResidueEquiv d hd m).injective
  apply Fin.ext
  simp [matchedCameraEquiv]

/-- A matched camera change followed by its reverse is exactly the identity. -/
@[simp] theorem matchedCameraEquiv_roundTrip
    (b c : ℕ) (hb : 1 < b) (hc : 1 < c) (k l : ℕ)
    (hcard : placeValue b k = placeValue c l)
    (digits : DigitWindow b hb k) :
    matchedCameraEquiv c b hc hb l k hcard.symm
        (matchedCameraEquiv b c hb hc k l hcard digits) = digits := by
  rw [← matchedCameraEquiv_symm b c hb hc k l hcard]
  exact (matchedCameraEquiv b c hb hc k l hcard).symm_apply_apply digits

/-! ## One-sided transport between windows of unequal cardinality -/

/--
Canonical value-preserving embedding of a finite positional window into a
window with at least as many residual states.
-/
def cameraEmbedding
    (b c : ℕ) (hb : 1 < b) (hc : 1 < c) (k l : ℕ)
    (hcard : placeValue b k ≤ placeValue c l) :
    DigitWindow b hb k ↪ DigitWindow c hc l :=
  (digitWindowResidueEquiv b hb k).toEmbedding.trans
    ((Fin.castLEEmb hcard).trans
      (digitWindowResidueEquiv c hc l).symm.toEmbedding)

/-- The camera embedding is the ordinary inclusion in residual coordinates. -/
theorem digitWindowResidueEquiv_cameraEmbedding
    (b c : ℕ) (hb : 1 < b) (hc : 1 < c) (k l : ℕ)
    (hcard : placeValue b k ≤ placeValue c l)
    (digits : DigitWindow b hb k) :
    digitWindowResidueEquiv c hc l
        (cameraEmbedding b c hb hc k l hcard digits) =
      Fin.castLE hcard (digitWindowResidueEquiv b hb k digits) := by
  simp [cameraEmbedding]

/-- A one-sided camera embedding preserves the represented natural number. -/
@[simp] theorem cameraEmbedding_preserves_value
    (b c : ℕ) (hb : 1 < b) (hc : 1 < c) (k l : ℕ)
    (hcard : placeValue b k ≤ placeValue c l)
    (digits : DigitWindow b hb k) :
    rawExpansionValue c (cameraEmbedding b c hb hc k l hcard digits).1 =
      rawExpansionValue b digits.1 := by
  rw [← digitWindowResidueEquiv_apply_val b hb k digits,
    ← digitWindowResidueEquiv_apply_val c hc l
      (cameraEmbedding b c hb hc k l hcard digits)]
  exact congrArg Fin.val
    (digitWindowResidueEquiv_cameraEmbedding b c hb hc k l hcard digits)

/-- Camera embeddings compose coherently through an intermediate window. -/
theorem cameraEmbedding_trans
    (b c d : ℕ) (hb : 1 < b) (hc : 1 < c) (hd : 1 < d)
    (k l m : ℕ)
    (hbc : placeValue b k ≤ placeValue c l)
    (hcd : placeValue c l ≤ placeValue d m) :
    (cameraEmbedding b c hb hc k l hbc).trans
        (cameraEmbedding c d hc hd l m hcd) =
      cameraEmbedding b d hb hd k m (hbc.trans hcd) := by
  apply Function.Embedding.ext
  intro digits
  apply (digitWindowResidueEquiv d hd m).injective
  apply Fin.ext
  simp [cameraEmbedding]

/-- At equal cardinality, the embedding is exactly the matched equivalence. -/
theorem cameraEmbedding_eq_matchedCameraEquiv_toEmbedding
    (b c : ℕ) (hb : 1 < b) (hc : 1 < c) (k l : ℕ)
    (hcard : placeValue b k = placeValue c l) :
    cameraEmbedding b c hb hc k l hcard.le =
      (matchedCameraEquiv b c hb hc k l hcard).toEmbedding := by
  apply Function.Embedding.ext
  intro digits
  apply (digitWindowResidueEquiv c hc l).injective
  apply Fin.ext
  simp [cameraEmbedding, matchedCameraEquiv]

/--
If the target has strictly more residual states, the canonical camera
embedding is not surjective.  Thus the one-sided construction cannot be
silently promoted to an equivalence.
-/
theorem cameraEmbedding_not_surjective
    (b c : ℕ) (hb : 1 < b) (hc : 1 < c) (k l : ℕ)
    (hcard : placeValue b k < placeValue c l) :
    ¬ Function.Surjective (cameraEmbedding b c hb hc k l hcard.le) := by
  intro hsurj
  let missingResidue : Fin (placeValue c l) :=
    ⟨placeValue b k, hcard⟩
  let missingDigits : DigitWindow c hc l :=
    (digitWindowResidueEquiv c hc l).symm missingResidue
  obtain ⟨digits, hdigits⟩ := hsurj missingDigits
  have hresidue := congrArg (digitWindowResidueEquiv c hc l) hdigits
  have hval := congrArg Fin.val hresidue
  have himpossible :
      (digitWindowResidueEquiv b hb k digits).val = placeValue b k := by
    simpa [missingDigits, missingResidue, cameraEmbedding] using hval
  exact (digitWindowResidueEquiv b hb k digits).isLt.ne himpossible

end

end CarryGeometry
