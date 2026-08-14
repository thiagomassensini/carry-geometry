import CarryGeometry.Mass
import CarryGeometry.WindowEquiv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

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

For a one-sided coordinate embedding, reindexing is replaced by extension by
zero.  The reverse map is then a retraction: reverse-after-forward is the
identity on the source, while forward-after-reverse is exactly projection
onto the embedded image.  These are the finite partial-isometry identities;
no inverse is asserted on the whole target.
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

/-- Extend a signal by zero along an injective coordinate map. -/
def pushforwardSignal (e : ι ↪ κ) (x : ι → ℝ) : κ → ℝ :=
  Function.extend e x 0

/-- Pushforward agrees with the original signal on the embedded image. -/
@[simp] theorem pushforwardSignal_apply
    (e : ι ↪ κ) (x : ι → ℝ) (i : ι) :
    pushforwardSignal e x (e i) = x i := by
  exact e.injective.extend_apply x 0 i

/-- Pushforward vanishes away from the embedded image. -/
theorem pushforwardSignal_eq_zero_of_not_mem_range
    (e : ι ↪ κ) (x : ι → ℝ) (j : κ)
    (hj : j ∉ Set.range e) :
    pushforwardSignal e x j = 0 := by
  apply Function.extend_apply'
  simpa only [Set.mem_range] using hj

/-- Restrict a target signal to the image coordinates of an embedding. -/
def restrictSignal (e : ι ↪ κ) (y : κ → ℝ) : ι → ℝ :=
  fun i => y (e i)

/-- Restriction is a left inverse to extension by zero. -/
@[simp] theorem restrictSignal_pushforwardSignal
    (e : ι ↪ κ) (x : ι → ℝ) :
    restrictSignal e (pushforwardSignal e x) = x := by
  funext i
  simp [restrictSignal]

/-- Projection of a target signal onto the coordinates in an embedded image. -/
def imageProjection (e : ι ↪ κ) (y : κ → ℝ) : κ → ℝ :=
  pushforwardSignal e (restrictSignal e y)

/-- The image projection fixes every embedded coordinate. -/
@[simp] theorem imageProjection_apply
    (e : ι ↪ κ) (y : κ → ℝ) (i : ι) :
    imageProjection e y (e i) = y (e i) := by
  simp [imageProjection, restrictSignal]

/-- The image projection vanishes away from the embedded coordinates. -/
theorem imageProjection_eq_zero_of_not_mem_range
    (e : ι ↪ κ) (y : κ → ℝ) (j : κ)
    (hj : j ∉ Set.range e) :
    imageProjection e y j = 0 := by
  exact pushforwardSignal_eq_zero_of_not_mem_range e (restrictSignal e y) j hj

/-- Extension followed by restriction defines an idempotent projection. -/
@[simp] theorem imageProjection_idempotent
    (e : ι ↪ κ) (y : κ → ℝ) :
    imageProjection e (imageProjection e y) = imageProjection e y := by
  unfold imageProjection
  rw [restrictSignal_pushforwardSignal]

/-- Apply the positional compression amplitude to every signal coordinate. -/
def compressSignal (b k : ℕ) (x : ι → ℝ) : ι → ℝ :=
  fun i => carryAmplitude b k * x i

@[simp] theorem compressSignal_apply
    (b k : ℕ) (x : ι → ℝ) (i : ι) :
    compressSignal b k x i = carryAmplitude b k * x i := rfl

/--
Compression-conjugated extension by zero along a coordinate embedding.
-/
def weightedEmbeddingTransform
    (e : ι ↪ κ) (b k c l : ℕ) (x : ι → ℝ) : κ → ℝ :=
  fun j =>
    (carryAmplitude c l)⁻¹ * pushforwardSignal e (compressSignal b k x) j

/--
Compression-conjugated restriction back to the source coordinates.
-/
def weightedEmbeddingRetract
    (e : ι ↪ κ) (b k c l : ℕ) (y : κ → ℝ) : ι → ℝ :=
  fun i =>
    (carryAmplitude b k)⁻¹ * restrictSignal e (compressSignal c l y) i

/-- Weighted extension intertwines source and target compression exactly. -/
theorem weightedEmbeddingTransform_intertwines
    (e : ι ↪ κ) (b k c l : ℕ) (hc : 0 < c) (x : ι → ℝ) :
    compressSignal c l (weightedEmbeddingTransform e b k c l x) =
      pushforwardSignal e (compressSignal b k x) := by
  funext j
  have hne : carryAmplitude c l ≠ 0 :=
    (carryAmplitude_pos c l hc).ne'
  simp [weightedEmbeddingTransform, compressSignal, hne, mul_assoc]

/-- Weighted restriction intertwines compression in the reverse direction. -/
theorem weightedEmbeddingRetract_intertwines
    (e : ι ↪ κ) (b k c l : ℕ) (hb : 0 < b) (y : κ → ℝ) :
    compressSignal b k (weightedEmbeddingRetract e b k c l y) =
      restrictSignal e (compressSignal c l y) := by
  funext i
  have hne : carryAmplitude b k ≠ 0 :=
    (carryAmplitude_pos b k hb).ne'
  simp [weightedEmbeddingRetract, compressSignal, restrictSignal, hne, mul_assoc]

/-- Reverse-after-forward is exactly the identity on the source signal. -/
@[simp] theorem weightedEmbeddingRetract_transform
    (e : ι ↪ κ) (b k c l : ℕ) (hb : 0 < b) (hc : 0 < c)
    (x : ι → ℝ) :
    weightedEmbeddingRetract e b k c l
        (weightedEmbeddingTransform e b k c l x) = x := by
  funext i
  have hbne : carryAmplitude b k ≠ 0 :=
    (carryAmplitude_pos b k hb).ne'
  have hcne : carryAmplitude c l ≠ 0 :=
    (carryAmplitude_pos c l hc).ne'
  simp [weightedEmbeddingRetract, weightedEmbeddingTransform,
    compressSignal, restrictSignal, hbne, hcne, mul_assoc]

/--
Forward-after-reverse is projection onto the embedded image, not the identity
on the whole target.
-/
theorem weightedEmbeddingTransform_retract
    (e : ι ↪ κ) (b k c l : ℕ) (hb : 0 < b) (hc : 0 < c)
    (y : κ → ℝ) :
    weightedEmbeddingTransform e b k c l
        (weightedEmbeddingRetract e b k c l y) = imageProjection e y := by
  funext j
  have hbne : carryAmplitude b k ≠ 0 :=
    (carryAmplitude_pos b k hb).ne'
  have hcne : carryAmplitude c l ≠ 0 :=
    (carryAmplitude_pos c l hc).ne'
  by_cases hj : ∃ i, e i = j
  · obtain ⟨i, rfl⟩ := hj
    simp [weightedEmbeddingTransform, weightedEmbeddingRetract,
      imageProjection, compressSignal, restrictSignal,
      hbne, hcne, mul_assoc]
  · have hj' : j ∉ Set.range e := by
      simpa only [Set.mem_range] using hj
    rw [imageProjection_eq_zero_of_not_mem_range e y j hj']
    simp [weightedEmbeddingTransform,
      pushforwardSignal_eq_zero_of_not_mem_range e _ j hj']

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

/-- Extension by zero along an embedding preserves counting quadratic energy. -/
theorem signalEnergy_pushforward
    [Fintype ι] [Fintype κ] (e : ι ↪ κ) (x : ι → ℝ) :
    signalEnergy (pushforwardSignal e x) = signalEnergy x := by
  classical
  unfold signalEnergy
  symm
  refine Finset.sum_of_injOn (s := Finset.univ) (t := Finset.univ)
    (fun i => e i) e.injective.injOn (by simp) ?_ ?_
  · intro j _ hj
    have hj' : j ∉ Set.range e := by
      rintro ⟨i, rfl⟩
      exact hj ⟨i, by simp, rfl⟩
    simp [pushforwardSignal_eq_zero_of_not_mem_range e x j hj']
  · intro i _
    simp

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

/-- Weighted extension preserves compressed quadratic energy. -/
theorem weightedEmbeddingTransform_preserves_compressedEnergy
    [Fintype ι] [Fintype κ]
    (e : ι ↪ κ) (b k c l : ℕ) (hc : 0 < c) (x : ι → ℝ) :
    compressedSignalEnergy c l (weightedEmbeddingTransform e b k c l x) =
      compressedSignalEnergy b k x := by
  unfold compressedSignalEnergy
  rw [weightedEmbeddingTransform_intertwines e b k c l hc x]
  exact signalEnergy_pushforward e (compressSignal b k x)

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

/-- Weighted extension transports the compressed bracket on embedded triples. -/
theorem weightedEmbeddingTransform_preserves_compressedBracket
    (e : ι ↪ κ) (b k c l : ℕ) (hc : 0 < c) (x : ι → ℝ)
    (left center right : ι) :
    carryAmplitude c l *
        centeredBracket (weightedEmbeddingTransform e b k c l x)
          (e left) (e center) (e right) =
      carryAmplitude b k * centeredBracket x left center right := by
  calc
    carryAmplitude c l *
          centeredBracket (weightedEmbeddingTransform e b k c l x)
            (e left) (e center) (e right) =
        centeredBracket
          (compressSignal c l (weightedEmbeddingTransform e b k c l x))
          (e left) (e center) (e right) := by
            symm
            exact centeredBracket_compressSignal c l
              (weightedEmbeddingTransform e b k c l x)
              (e left) (e center) (e right)
    _ = centeredBracket (pushforwardSignal e (compressSignal b k x))
          (e left) (e center) (e right) := by
            rw [weightedEmbeddingTransform_intertwines e b k c l hc x]
    _ = centeredBracket (compressSignal b k x) left center right := by
          simp [centeredBracket]
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

/-! ## Specialization to one-sided positional windows -/

/-- Weighted extension induced by a value-preserving camera embedding. -/
def embeddedWeightedCameraTransform
    (b c : ℕ) (hb : 1 < b) (hc : 1 < c) (k l : ℕ)
    (hcard : placeValue b k ≤ placeValue c l)
    (x : DigitWindow b hb k → ℝ) : DigitWindow c hc l → ℝ :=
  weightedEmbeddingTransform (cameraEmbedding b c hb hc k l hcard)
    b k c l x

/-- Weighted restriction back from an embedded positional camera. -/
def embeddedWeightedCameraRetract
    (b c : ℕ) (hb : 1 < b) (hc : 1 < c) (k l : ℕ)
    (hcard : placeValue b k ≤ placeValue c l)
    (y : DigitWindow c hc l → ℝ) : DigitWindow b hb k → ℝ :=
  weightedEmbeddingRetract (cameraEmbedding b c hb hc k l hcard)
    b k c l y

/-- Embedded positional transport preserves compressed quadratic energy. -/
theorem embeddedWeightedCameraTransform_preserves_compressedEnergy
    (b c : ℕ) (hb : 1 < b) (hc : 1 < c) (k l : ℕ)
    (hcard : placeValue b k ≤ placeValue c l)
    (x : DigitWindow b hb k → ℝ) :
    compressedSignalEnergy c l
        (embeddedWeightedCameraTransform b c hb hc k l hcard x) =
      compressedSignalEnergy b k x := by
  exact weightedEmbeddingTransform_preserves_compressedEnergy
    (cameraEmbedding b c hb hc k l hcard) b k c l
    (lt_trans Nat.zero_lt_one hc) x

/-- Restriction after embedded positional transport recovers the source. -/
@[simp] theorem embeddedWeightedCameraRetract_transform
    (b c : ℕ) (hb : 1 < b) (hc : 1 < c) (k l : ℕ)
    (hcard : placeValue b k ≤ placeValue c l)
    (x : DigitWindow b hb k → ℝ) :
    embeddedWeightedCameraRetract b c hb hc k l hcard
        (embeddedWeightedCameraTransform b c hb hc k l hcard x) = x := by
  exact weightedEmbeddingRetract_transform
    (cameraEmbedding b c hb hc k l hcard) b k c l
    (lt_trans Nat.zero_lt_one hb) (lt_trans Nat.zero_lt_one hc) x

/--
Transport after restriction is precisely projection onto the embedded camera
image.
-/
theorem embeddedWeightedCameraTransform_retract
    (b c : ℕ) (hb : 1 < b) (hc : 1 < c) (k l : ℕ)
    (hcard : placeValue b k ≤ placeValue c l)
    (y : DigitWindow c hc l → ℝ) :
    embeddedWeightedCameraTransform b c hb hc k l hcard
        (embeddedWeightedCameraRetract b c hb hc k l hcard y) =
      imageProjection (cameraEmbedding b c hb hc k l hcard) y := by
  exact weightedEmbeddingTransform_retract
    (cameraEmbedding b c hb hc k l hcard) b k c l
    (lt_trans Nat.zero_lt_one hb) (lt_trans Nat.zero_lt_one hc) y

end

end CarryGeometry
