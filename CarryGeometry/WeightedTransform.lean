import CarryGeometry.Mass
import CarryGeometry.WindowEquiv
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Compression-weighted transport between finite cameras

An equivalence of finite coordinates reindexes a signal without changing its
counting energy.  A positional camera also carries the distinguished
compression weight `carryAmplitude b k = b ^ (-k / 2)`.  The weighted camera
transform is the conjugation

`C_target⁻¹ ∘ P ∘ C_source`,

where `P` is reindexing and `C` multiplies every coordinate by the camera
amplitude.  The main intertwining theorem states exactly

`C_target (T x) = P (C_source x)`.

Thus the result distinguishes two claims:

* the coordinate map is an actual `Equiv`;
* the conjugated signal map preserves compressed quadratic energy.
-/

namespace CarryGeometry

noncomputable section

open scoped BigOperators

variable {ι κ ν : Type*}

/-- Reindex a signal along an exact equivalence of coordinate types. -/
def reindexSignal (e : ι ≃ κ) (x : ι → ℝ) : κ → ℝ :=
  fun j => x (e.symm j)

@[simp] theorem reindexSignal_apply
    (e : ι ≃ κ) (x : ι → ℝ) (j : κ) :
    reindexSignal e x j = x (e.symm j) := rfl

/-- Apply the positional compression amplitude to every signal coordinate. -/
def compressSignal (b k : ℕ) (x : ι → ℝ) : ι → ℝ :=
  fun i => carryAmplitude b k * x i

@[simp] theorem compressSignal_apply
    (b k : ℕ) (x : ι → ℝ) (i : ι) :
    compressSignal b k x i = carryAmplitude b k * x i := rfl

/--
Transport a signal by conjugating coordinate reindexing with the source and
target compression weights.
-/
def weightedCameraTransform
    (e : ι ≃ κ) (b k c l : ℕ) (x : ι → ℝ) : κ → ℝ :=
  fun j =>
    (carryAmplitude c l)⁻¹ * carryAmplitude b k * x (e.symm j)

/-- The weighted transform intertwines the two compression maps exactly. -/
theorem weightedCameraTransform_intertwines
    (e : ι ≃ κ) (b k c l : ℕ) (hc : 0 < c) (x : ι → ℝ) :
    compressSignal c l (weightedCameraTransform e b k c l x) =
      reindexSignal e (compressSignal b k x) := by
  funext j
  have hne : carryAmplitude c l ≠ 0 :=
    (carryAmplitude_pos c l hc).ne'
  simp [weightedCameraTransform, compressSignal, reindexSignal, hne, mul_assoc]

/-- Reversing both the coordinate equivalence and the weights gives the identity. -/
@[simp] theorem weightedCameraTransform_roundTrip
    (e : ι ≃ κ) (b k c l : ℕ) (hb : 0 < b) (hc : 0 < c)
    (x : ι → ℝ) :
    weightedCameraTransform e.symm c l b k
        (weightedCameraTransform e b k c l x) = x := by
  funext i
  have hbne : carryAmplitude b k ≠ 0 :=
    (carryAmplitude_pos b k hb).ne'
  have hcne : carryAmplitude c l ≠ 0 :=
    (carryAmplitude_pos c l hc).ne'
  simp [weightedCameraTransform, hbne, hcne, mul_assoc]

/-- Weighted camera transforms compose coherently through an intermediate camera. -/
theorem weightedCameraTransform_trans
    (e : ι ≃ κ) (f : κ ≃ ν)
    (b k c l d m : ℕ) (hc : 0 < c) (x : ι → ℝ) :
    weightedCameraTransform (e.trans f) b k d m x =
      weightedCameraTransform f c l d m
        (weightedCameraTransform e b k c l x) := by
  funext j
  have hcne : carryAmplitude c l ≠ 0 :=
    (carryAmplitude_pos c l hc).ne'
  simp [weightedCameraTransform, hcne, mul_assoc]

/-- Counting quadratic energy of a finite real signal. -/
def signalEnergy [Fintype ι] (x : ι → ℝ) : ℝ :=
  ∑ i, (x i) ^ 2

/-- Exact reindexing preserves counting quadratic energy. -/
theorem signalEnergy_reindex
    [Fintype ι] [Fintype κ] (e : ι ≃ κ) (x : ι → ℝ) :
    signalEnergy (reindexSignal e x) = signalEnergy x := by
  simpa only [signalEnergy, reindexSignal] using
    e.symm.sum_comp (fun i => (x i) ^ 2)

/-- Quadratic energy after applying a camera's compression weight. -/
def compressedSignalEnergy [Fintype ι]
    (b k : ℕ) (x : ι → ℝ) : ℝ :=
  signalEnergy (compressSignal b k x)

/-- The weighted camera transform preserves compressed quadratic energy. -/
theorem weightedCameraTransform_preserves_compressedEnergy
    [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (b k c l : ℕ) (hc : 0 < c) (x : ι → ℝ) :
    compressedSignalEnergy c l (weightedCameraTransform e b k c l x) =
      compressedSignalEnergy b k x := by
  unfold compressedSignalEnergy
  rw [weightedCameraTransform_intertwines e b k c l hc x]
  exact signalEnergy_reindex e (compressSignal b k x)

/-- The centered three-point second difference used by the positional bracket. -/
def centeredBracket
    (x : ι → ℝ) (left center right : ι) : ℝ :=
  x left - 2 * x center + x right

/-- Compression can be pulled outside the centered bracket. -/
theorem centeredBracket_compressSignal
    (b k : ℕ) (x : ι → ℝ) (left center right : ι) :
    centeredBracket (compressSignal b k x) left center right =
      carryAmplitude b k * centeredBracket x left center right := by
  simp [centeredBracket, compressSignal]
  ring

/-- The weighted transform transports the compressed centered bracket exactly. -/
theorem weightedCameraTransform_preserves_compressedBracket
    (e : ι ≃ κ) (b k c l : ℕ) (hc : 0 < c) (x : ι → ℝ)
    (left center right : ι) :
    carryAmplitude c l *
        centeredBracket (weightedCameraTransform e b k c l x)
          (e left) (e center) (e right) =
      carryAmplitude b k * centeredBracket x left center right := by
  calc
    carryAmplitude c l *
          centeredBracket (weightedCameraTransform e b k c l x)
            (e left) (e center) (e right) =
        centeredBracket
          (compressSignal c l (weightedCameraTransform e b k c l x))
          (e left) (e center) (e right) := by
            symm
            exact centeredBracket_compressSignal c l
              (weightedCameraTransform e b k c l x)
              (e left) (e center) (e right)
    _ = centeredBracket (reindexSignal e (compressSignal b k x))
          (e left) (e center) (e right) := by
            rw [weightedCameraTransform_intertwines e b k c l hc x]
    _ = centeredBracket (compressSignal b k x) left center right := by
          simp [centeredBracket, reindexSignal]
    _ = carryAmplitude b k * centeredBracket x left center right :=
          centeredBracket_compressSignal b k x left center right

/-! ## Specialization to matched positional windows -/

/-- Weighted transform induced by an exact matched-camera equivalence. -/
def matchedWeightedCameraTransform
    (b c : ℕ) (hb : 1 < b) (hc : 1 < c) (k l : ℕ)
    (hcard : placeValue b k = placeValue c l)
    (x : DigitWindow b hb k → ℝ) : DigitWindow c hc l → ℝ :=
  weightedCameraTransform (matchedCameraEquiv b c hb hc k l hcard)
    b k c l x

/-- Matched weighted transport preserves compressed quadratic energy. -/
theorem matchedWeightedCameraTransform_preserves_compressedEnergy
    (b c : ℕ) (hb : 1 < b) (hc : 1 < c) (k l : ℕ)
    (hcard : placeValue b k = placeValue c l)
    (x : DigitWindow b hb k → ℝ) :
    compressedSignalEnergy c l
        (matchedWeightedCameraTransform b c hb hc k l hcard x) =
      compressedSignalEnergy b k x := by
  exact weightedCameraTransform_preserves_compressedEnergy
    (matchedCameraEquiv b c hb hc k l hcard) b k c l
    (lt_trans Nat.zero_lt_one hc) x

/-- Matched weighted transport preserves the compressed centered bracket. -/
theorem matchedWeightedCameraTransform_preserves_compressedBracket
    (b c : ℕ) (hb : 1 < b) (hc : 1 < c) (k l : ℕ)
    (hcard : placeValue b k = placeValue c l)
    (x : DigitWindow b hb k → ℝ)
    (left center right : DigitWindow b hb k) :
    carryAmplitude c l *
        centeredBracket
          (matchedWeightedCameraTransform b c hb hc k l hcard x)
          (matchedCameraEquiv b c hb hc k l hcard left)
          (matchedCameraEquiv b c hb hc k l hcard center)
          (matchedCameraEquiv b c hb hc k l hcard right) =
      carryAmplitude b k * centeredBracket x left center right := by
  exact weightedCameraTransform_preserves_compressedBracket
    (matchedCameraEquiv b c hb hc k l hcard) b k c l
    (lt_trans Nat.zero_lt_one hc) x left center right

end

end CarryGeometry
