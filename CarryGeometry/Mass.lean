import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Positional carry mass and amplitudes

This module contains only the three scalar laws used by the foundational
carry geometry.  No primality, operator, spectral, or analytic-continuation
structure enters these definitions.
-/

namespace CarryGeometry

noncomputable section

/-- Positional carry mass at base `b` and depth `k`: `b⁻ᵏ`. -/
def carryMass (b k : ℕ) : ℝ :=
  (b : ℝ) ^ (-((k : ℝ)))

/-- Distinguished nonnegative quadratic amplitude: `b⁻ᵏ⁄²`. -/
def carryAmplitude (b k : ℕ) : ℝ :=
  (b : ℝ) ^ (-((k : ℝ)) / 2)

/-- Deformed positional amplitude at exponent `sigma`: `b⁻ᵏˢⁱᵍᵐᵃ`. -/
def deformedAmplitude (b : ℕ) (sigma : ℝ) (k : ℕ) : ℝ :=
  (b : ℝ) ^ (-((k : ℝ)) * sigma)

/-- The distinguished carry amplitude is nonnegative. -/
theorem carryAmplitude_nonneg (b k : ℕ) :
    0 ≤ carryAmplitude b k := by
  unfold carryAmplitude
  exact Real.rpow_nonneg (by positivity) _

/-- The distinguished amplitude is strictly positive for every positive base. -/
theorem carryAmplitude_pos (b k : ℕ) (hb : 0 < b) :
    0 < carryAmplitude b k := by
  unfold carryAmplitude
  exact Real.rpow_pos_of_pos (by exact_mod_cast hb) _

/-- The distinguished amplitude is exactly a quadratic root of carry mass. -/
@[simp] theorem carryAmplitude_sq_eq_carryMass (b k : ℕ) :
    (carryAmplitude b k) ^ 2 = carryMass b k := by
  unfold carryAmplitude carryMass
  have hb0 : 0 ≤ (b : ℝ) := by positivity
  rw [← Real.rpow_mul_natCast hb0 (-((k : ℝ)) / 2) 2]
  congr 1
  ring

/-- At the critical exponent, the deformed amplitude is the carry amplitude. -/
@[simp] theorem deformedAmplitude_half (b k : ℕ) :
    deformedAmplitude b ((1 : ℝ) / 2) k = carryAmplitude b k := by
  unfold deformedAmplitude carryAmplitude
  congr 1
  ring

/-! ## Sharp semantic boundaries -/

/-- At depth zero no mass decay has occurred. -/
@[simp] theorem carryMass_zero_depth (b : ℕ) :
    carryMass b 0 = 1 := by
  simp [carryMass]

/-- At depth zero every deformation has amplitude one. -/
@[simp] theorem deformedAmplitude_zero_depth (b : ℕ) (sigma : ℝ) :
    deformedAmplitude b sigma 0 = 1 := by
  simp [deformedAmplitude]

/-- Base one has no positional mass decay. -/
@[simp] theorem carryMass_base_one (k : ℕ) :
    carryMass 1 k = 1 := by
  simp [carryMass]

/-- Every deformation is trivial at base one. -/
@[simp] theorem deformedAmplitude_base_one (sigma : ℝ) (k : ℕ) :
    deformedAmplitude 1 sigma k = 1 := by
  simp [deformedAmplitude]

end

end CarryGeometry
