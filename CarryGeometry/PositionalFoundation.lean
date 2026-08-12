import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-!
# Positional foundation

This module is the logical beginning of the library.  It does not postulate a
carry law.  Starting from natural-number powers, Euclidean division, and
congruence modulo the place value `b ^ k`, it defines positional language and
derives carry propagation.

The object of departure is an ordinary finite positional base.  The
mathematically genuine regime is `1 < b`; several arithmetic decomposition
results need only the weaker nondegeneracy condition `0 < b`.
-/

namespace CarryGeometry

/-- Value of the first `k` positional places in base `b`. -/
def placeValue (b k : ℕ) : ℕ :=
  b ^ k

/-- Quotient left after removing the lowest `k` base-`b` places. -/
def quotientAtDepth (b k n : ℕ) : ℕ :=
  n / placeValue b k

/-- Value represented by the lowest `k` base-`b` places. -/
def residueAtDepth (b k n : ℕ) : ℕ :=
  n % placeValue b k

/-- The lowest `k` places are saturated when their residue is `b ^ k - 1`. -/
def lowerPositionsSaturated (b k n : ℕ) : Prop :=
  n ≡ placeValue b k - 1 [MOD placeValue b k]

/-- Adding one carries through the lowest `k` places when the new residue is zero. -/
def carryAfterIncrementAtDepth (b k n : ℕ) : Prop :=
  n + 1 ≡ 0 [MOD placeValue b k]

/-- The carry reaches depth `k`, but not the next positional place. -/
def firstCarryDepth (b k n : ℕ) : Prop :=
  carryAfterIncrementAtDepth b k n ∧
    ¬carryAfterIncrementAtDepth b (k + 1) n

/-- A positive base has a positive value at every positional depth. -/
theorem placeValue_pos (b k : ℕ) (hb : 0 < b) :
    0 < placeValue b k := by
  exact pow_pos hb k

/-- Moving one place multiplies the positional value by the base. -/
@[simp] theorem placeValue_succ (b k : ℕ) :
    placeValue b (k + 1) = placeValue b k * b := by
  simp [placeValue, pow_succ]

/-- Quotient and residue reconstruct the original natural number. -/
theorem positionalDecompositionAtDepth
    (b k n : ℕ) (hb : 0 < b) :
    residueAtDepth b k n +
        placeValue b k * quotientAtDepth b k n = n ∧
      residueAtDepth b k n < placeValue b k := by
  have hplace : 0 < placeValue b k := placeValue_pos b k hb
  exact (Nat.div_mod_unique hplace).1 ⟨rfl, rfl⟩

/-- The canonical quotient--residue decomposition is unique. -/
theorem positionalDecompositionAtDepth_existsUnique
    (b k n : ℕ) (hb : 0 < b) :
    ∃! qr : ℕ × ℕ,
      qr.2 + placeValue b k * qr.1 = n ∧
        qr.2 < placeValue b k := by
  have hplace : 0 < placeValue b k := placeValue_pos b k hb
  refine
    ⟨(quotientAtDepth b k n, residueAtDepth b k n),
      positionalDecompositionAtDepth b k n hb, ?_⟩
  rintro ⟨q, r⟩ hqr
  have hcanonical :
      n / placeValue b k = q ∧ n % placeValue b k = r :=
    (Nat.div_mod_unique hplace).2 hqr
  apply Prod.ext
  · exact hcanonical.1.symm
  · exact hcanonical.2.symm

/-- Saturation is exactly the last residue in the depth-`k` window. -/
theorem lowerPositionsSaturated_iff_residue_eq_last
    (b k n : ℕ) (hb : 0 < b) :
    lowerPositionsSaturated b k n ↔
      residueAtDepth b k n = placeValue b k - 1 := by
  have hplace : 0 < placeValue b k := placeValue_pos b k hb
  have hlast : placeValue b k - 1 < placeValue b k :=
    Nat.sub_lt hplace Nat.zero_lt_one
  unfold lowerPositionsSaturated residueAtDepth
  rw [Nat.ModEq, Nat.mod_eq_of_lt hlast]

/--
Positional carry propagation.

Adding one carries through the lowest `k` places if and only if those places
were saturated before the increment.
-/
theorem increment_carries_iff_lowerPositionsSaturated
    (b k n : ℕ) (hb : 0 < b) :
    carryAfterIncrementAtDepth b k n ↔
      lowerPositionsSaturated b k n := by
  have hplace : 0 < placeValue b k := placeValue_pos b k hb
  have hone : 1 ≤ placeValue b k :=
    Nat.one_le_iff_ne_zero.mpr (ne_of_gt hplace)
  have hlast : placeValue b k - 1 + 1 = placeValue b k :=
    Nat.sub_add_cancel hone
  unfold carryAfterIncrementAtDepth lowerPositionsSaturated
  constructor
  · intro hcarry
    have htarget :
        n + 1 ≡ placeValue b k - 1 + 1 [MOD placeValue b k] := by
      simpa [hlast, Nat.ModEq] using hcarry
    exact Nat.ModEq.add_right_cancel' 1 htarget
  · intro hsaturated
    have hadd := hsaturated.add_right 1
    simpa [hlast, Nat.ModEq] using hadd

/-- Carry propagation is equivalent to reset of the lower positional block. -/
theorem carryAfterIncrementAtDepth_iff_residue_eq_zero
    (b k n : ℕ) :
    carryAfterIncrementAtDepth b k n ↔
      residueAtDepth b k (n + 1) = 0 := by
  simp [carryAfterIncrementAtDepth, residueAtDepth, Nat.ModEq]

/-- Carry through `k` places is divisibility of the incremented number by `b ^ k`. -/
theorem carryAfterIncrementAtDepth_iff_placeValue_dvd
    (b k n : ℕ) :
    carryAfterIncrementAtDepth b k n ↔
      placeValue b k ∣ n + 1 := by
  rw [carryAfterIncrementAtDepth_iff_residue_eq_zero]
  exact Nat.dvd_iff_mod_eq_zero.symm

/-- Carry through `k` places produces an integral upper-place quotient. -/
theorem carryAfterIncrementAtDepth_iff_exists_upperValue
    (b k n : ℕ) :
    carryAfterIncrementAtDepth b k n ↔
      ∃ q : ℕ, n + 1 = placeValue b k * q := by
  rw [carryAfterIncrementAtDepth_iff_placeValue_dvd]
  rfl

/-- Exact carry depth means divisibility by one place value but not the next. -/
theorem firstCarryDepth_iff_divisible_not_next
    (b k n : ℕ) :
    firstCarryDepth b k n ↔
      placeValue b k ∣ n + 1 ∧
        ¬placeValue b (k + 1) ∣ n + 1 := by
  simp only [firstCarryDepth,
    carryAfterIncrementAtDepth_iff_placeValue_dvd]

/--
The saturated depth-`k` block is the primitive carry computation:
adding one resets its residue to zero and transfers exactly one unit above it.
-/
theorem saturatedBlock_increment_resets_and_carries_one
    (b k : ℕ) (hb : 0 < b) :
    residueAtDepth b k (placeValue b k - 1 + 1) = 0 ∧
      quotientAtDepth b k (placeValue b k - 1 + 1) = 1 := by
  have hplace : 0 < placeValue b k := placeValue_pos b k hb
  have hone : 1 ≤ placeValue b k :=
    Nat.one_le_iff_ne_zero.mpr (ne_of_gt hplace)
  have hlast : placeValue b k - 1 + 1 = placeValue b k :=
    Nat.sub_add_cancel hone
  rw [hlast]
  constructor
  · exact Nat.mod_self _
  · exact Nat.div_self hplace

end CarryGeometry
