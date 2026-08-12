import CarryGeometry.PositionalFoundation
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Forced positional normalization

A raw coefficient may be any natural number, so it continues to define a
perfectly valid weighted sum even when it is not a base-`b` digit.  This module
separates that unrestricted algebraic representation from the finite digit
alphabet and proves that value-preserving normalization is unique.

At one position the unique split is

`a = (a % b) + b * (a / b)`.

The first term is the restored digit; the second factor is the forced carry.
-/

namespace CarryGeometry

/-- A coefficient is an admissible base-`b` digit exactly when it is below `b`. -/
def IsAdmissibleDigit (b a : ℕ) : Prop :=
  a < b

/-- The unique admissible digit obtained from a raw coefficient. -/
def normalizedDigit (b a : ℕ) : ℕ :=
  a % b

/-- Number of units transferred to the next positional scale. -/
def carryUnits (b a : ℕ) : ℕ :=
  a / b

/-- A value-preserving split of a coefficient into a bounded digit and carry. -/
def IsCoefficientNormalization
    (b a digit carry : ℕ) : Prop :=
  digit < b ∧ digit + b * carry = a

/-- Euclidean division gives the coefficient split into digit and carry. -/
theorem coefficient_decomposition (b a : ℕ) :
    normalizedDigit b a + b * carryUnits b a = a := by
  exact Nat.mod_add_div a b

/--
The bounded value-preserving coefficient split is unique.  Consequently,
neither its normalized digit nor its carry can be chosen differently.
-/
theorem coefficient_normalization_unique
    (b a digit carry : ℕ) (hb : 0 < b) :
    IsCoefficientNormalization b a digit carry ↔
      digit = normalizedDigit b a ∧ carry = carryUnits b a := by
  constructor
  · rintro ⟨hdigit, hvalue⟩
    have hcanonical : a / b = carry ∧ a % b = digit :=
      (Nat.div_mod_unique hb).2 ⟨hvalue, hdigit⟩
    exact ⟨hcanonical.2.symm, hcanonical.1.symm⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨Nat.mod_lt a hb, coefficient_decomposition b a⟩

/-- Normalization preserves the value of a coefficient at every position. -/
theorem weighted_coefficient_normalization
    (b a j : ℕ) :
    a * placeValue b j =
      normalizedDigit b a * placeValue b j +
        carryUnits b a * placeValue b (j + 1) := by
  calc
    a * placeValue b j =
        (normalizedDigit b a + b * carryUnits b a) * placeValue b j := by
      rw [coefficient_decomposition]
    _ = normalizedDigit b a * placeValue b j +
        carryUnits b a * placeValue b (j + 1) := by
      rw [placeValue_succ]
      ring

/-- An admissible coefficient produces no carry, and only such a coefficient does. -/
theorem carryUnits_eq_zero_iff_admissible
    (b a : ℕ) (hb : 0 < b) :
    carryUnits b a = 0 ↔ IsAdmissibleDigit b a := by
  unfold carryUnits IsAdmissibleDigit
  rw [Nat.div_eq_zero_iff]
  simp [ne_of_gt hb]

/-- Coefficient overflow is equivalent to a strictly positive carry. -/
theorem overflow_iff_carryUnits_pos
    (b a : ℕ) (hb : 0 < b) :
    b ≤ a ↔ 0 < carryUnits b a := by
  constructor
  · intro hoverflow
    exact Nat.div_pos hoverflow hb
  · intro hcarry
    by_contra hnot
    have hadmissible : a < b := Nat.lt_of_not_ge hnot
    have hzero : carryUnits b a = 0 :=
      (carryUnits_eq_zero_iff_admissible b a hb).2 hadmissible
    omega

/--
For every genuine base, the finite digit alphabet is not closed under raw
addition.  Thus closure cannot be obtained by keeping each coefficient in the
same position without normalization.
-/
theorem finiteDigitAlphabet_not_closed_under_raw_addition
    (b : ℕ) (hb : 1 < b) :
    ∃ x y : ℕ,
      IsAdmissibleDigit b x ∧ IsAdmissibleDigit b y ∧
        ¬IsAdmissibleDigit b (x + y) := by
  refine ⟨b - 1, 1, ?_, hb, ?_⟩
  · exact Nat.sub_lt (lt_trans Nat.zero_lt_one hb) Nat.zero_lt_one
  · unfold IsAdmissibleDigit
    omega

/-- For bases above two, the finite digit alphabet is also not closed under raw multiplication. -/
theorem finiteDigitAlphabet_not_closed_under_raw_multiplication
    (b : ℕ) (hb : 2 < b) :
    ∃ x y : ℕ,
      IsAdmissibleDigit b x ∧ IsAdmissibleDigit b y ∧
        ¬IsAdmissibleDigit b (x * y) := by
  have hb0 : 0 < b := by omega
  have hmax : b - 1 < b := Nat.sub_lt hb0 Nat.zero_lt_one
  refine ⟨b - 1, b - 1, hmax, hmax, ?_⟩
  unfold IsAdmissibleDigit
  have hone : 1 ≤ b := by omega
  have hsub : b - 1 + 1 = b := Nat.sub_add_cancel hone
  nlinarith

/-- The maximal digit plus one normalizes to digit zero and one carry unit. -/
theorem maxDigit_add_one_normalizes
    (b : ℕ) (hb : 0 < b) :
    normalizedDigit b (b - 1 + 1) = 0 ∧
      carryUnits b (b - 1 + 1) = 1 := by
  have hone : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr (ne_of_gt hb)
  rw [Nat.sub_add_cancel hone]
  exact ⟨Nat.mod_self b, Nat.div_self hb⟩

/-! ## Global raw expansions and canonical normalization -/

/--
Value of a finite raw coefficient list, ordered from least to most significant.
No bound on its coefficients is imposed.
-/
def rawExpansionValue
    (b : ℕ) (coefficients : List ℕ) : ℕ :=
  Nat.ofDigits b coefficients

/-- A raw coefficient list is exactly its unrestricted positional weighted sum. -/
theorem rawExpansionValue_eq_weightedSum
    (b : ℕ) (coefficients : List ℕ) :
    rawExpansionValue b coefficients =
      (coefficients.mapIdx fun j a => a * b ^ j).sum := by
  exact Nat.ofDigits_eq_sum_mapIdx b coefficients

/-- Canonical finite-alphabet digit list representing the same raw value. -/
def normalizeCoefficients
    (b : ℕ) (coefficients : List ℕ) : List ℕ :=
  Nat.digits b (rawExpansionValue b coefficients)

/-- Global normalization does not change the represented natural number. -/
theorem normalizeCoefficients_preserves_value
    (b : ℕ) (coefficients : List ℕ) :
    rawExpansionValue b (normalizeCoefficients b coefficients) =
      rawExpansionValue b coefficients := by
  exact Nat.ofDigits_digits b (rawExpansionValue b coefficients)

/-- Every coefficient produced by normalization belongs to the finite alphabet. -/
theorem normalizeCoefficients_digits_admissible
    (b : ℕ) (hb : 1 < b) (coefficients : List ℕ) :
    ∀ digit ∈ normalizeCoefficients b coefficients,
      IsAdmissibleDigit b digit := by
  intro digit hdigit
  exact Nat.digits_lt_base hb hdigit

/-- A nonempty normalized list has no zero in its most significant position. -/
theorem normalizeCoefficients_no_leading_zero
    (b : ℕ) (coefficients : List ℕ) :
    ∀ h : normalizeCoefficients b coefficients ≠ [],
      (normalizeCoefficients b coefficients).getLast h ≠ 0 := by
  intro h
  unfold normalizeCoefficients at h ⊢
  exact Nat.getLast_digit_ne_zero b
    ((Nat.digits_ne_nil_iff_ne_zero).mp h)

/-- An already admissible canonical digit list is fixed by normalization. -/
theorem normalizeCoefficients_eq_self
    (b : ℕ) (hb : 1 < b) (coefficients : List ℕ)
    (hdigits : ∀ digit ∈ coefficients, IsAdmissibleDigit b digit)
    (hleading : ∀ h : coefficients ≠ [], coefficients.getLast h ≠ 0) :
    normalizeCoefficients b coefficients = coefficients := by
  exact Nat.digits_ofDigits b hb coefficients hdigits hleading

/-! ## Finite alphabet and exponential positional compression -/

/-- All admissible strings of exactly `k` base-`b` digits. -/
noncomputable def admissibleDigitStrings
    (b : ℕ) (hb : 1 < b) (k : ℕ) : Finset (List ℕ) :=
  List.fixedLengthDigits hb k

/-- `k` finite base-`b` positions contain exactly `b ^ k` states. -/
@[simp] theorem card_admissibleDigitStrings
    (b : ℕ) (hb : 1 < b) (k : ℕ) :
    (admissibleDigitStrings b hb k).card = placeValue b k := by
  exact List.card_fixedLengthDigits hb k

/-- Evaluation bijects admissible `k`-digit strings with the interval `[0, b ^ k)`. -/
theorem eval_bijects_admissibleDigitStrings_and_residues
    (b : ℕ) (hb : 1 < b) (k : ℕ) :
    Set.BijOn (rawExpansionValue b)
      (admissibleDigitStrings b hb k : Set (List ℕ))
      (Finset.range (placeValue b k) : Set ℕ) := by
  exact Nat.bijOn_ofDigits' hb k

/--
Finite-alphabet positional normalization is forced.

The canonical split exists, admissibility is exactly absence of carry,
overflow is exactly positive carry, and every other bounded value-preserving
split equals the canonical one.
-/
theorem finiteAlphabetNormalization_forced
    (b a : ℕ) (hb : 0 < b) :
    IsCoefficientNormalization b a
        (normalizedDigit b a) (carryUnits b a) ∧
      (IsAdmissibleDigit b a ↔ carryUnits b a = 0) ∧
      (b ≤ a ↔ 0 < carryUnits b a) ∧
      ∀ digit carry : ℕ,
        IsCoefficientNormalization b a digit carry →
          digit = normalizedDigit b a ∧ carry = carryUnits b a := by
  refine ⟨?_, ?_, overflow_iff_carryUnits_pos b a hb, ?_⟩
  · exact (coefficient_normalization_unique b a
      (normalizedDigit b a) (carryUnits b a) hb).2 ⟨rfl, rfl⟩
  · exact (carryUnits_eq_zero_iff_admissible b a hb).symm
  · intro digit carry hnormalization
    exact (coefficient_normalization_unique b a digit carry hb).1 hnormalization

end CarryGeometry
