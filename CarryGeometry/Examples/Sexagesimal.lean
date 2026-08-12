import CarryGeometry.Normalization

/-!
# Sexagesimal normalization examples

Lean's coefficient lists are ordered from least to most significant.  Reversing
the displayed list gives the usual human-readable most-significant-first
notation used in the accompanying documentation.
-/

namespace CarryGeometry.Examples.Sexagesimal

open CarryGeometry

/-- `59 + 2 = 61` normalizes to conventional sexagesimal `[1, 1]`. -/
theorem fiftyNine_add_two :
    normalizeCoefficients 60 [59 + 2] = [1, 1] := by
  norm_num [normalizeCoefficients, rawExpansionValue]

/-- `59 * 59 = 3481` normalizes internally to `[1, 58]`, hence conventionally `[58, 1]`. -/
theorem fiftyNine_mul_fiftyNine :
    normalizeCoefficients 60 [59 * 59] = [1, 58] := by
  norm_num [normalizeCoefficients, rawExpansionValue]

/-- `59 ^ 3 = 205379` normalizes internally to `[59, 2, 57]`, hence conventionally `[57, 2, 59]`. -/
theorem fiftyNine_pow_three :
    normalizeCoefficients 60 [59 ^ 3] = [59, 2, 57] := by
  norm_num [normalizeCoefficients, rawExpansionValue]

/-- Conventional most-significant-first rendering of `59 * 59`. -/
theorem fiftyNine_mul_fiftyNine_conventional :
    (normalizeCoefficients 60 [59 * 59]).reverse = [58, 1] := by
  norm_num [normalizeCoefficients, rawExpansionValue]

/-- Conventional most-significant-first rendering of `59 ^ 3`. -/
theorem fiftyNine_pow_three_conventional :
    (normalizeCoefficients 60 [59 ^ 3]).reverse = [57, 2, 59] := by
  norm_num [normalizeCoefficients, rawExpansionValue]

end CarryGeometry.Examples.Sexagesimal
