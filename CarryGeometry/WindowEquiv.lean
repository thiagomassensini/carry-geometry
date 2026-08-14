import CarryGeometry.Normalization

/-!
# Finite positional windows as exact equivalences

The normalization layer proves that evaluation is bijective from admissible
base-`b` strings of length `k` to the residual interval `[0, b ^ k)`.  This
module packages that theorem as an `Equiv` with `Fin (b ^ k)` and uses it to
define exact coordinate changes between windows of equal cardinality.

No equality of cardinalities is manufactured: a finite camera change is an
equivalence only when the two place values are equal.
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

end

end CarryGeometry
