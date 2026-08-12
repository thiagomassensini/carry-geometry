import CarryGeometry.Mass

/-!
# Quadratic rigidity of positional amplitudes

For a genuine positional base and a positive depth, matching the quadratic
energy of `deformedAmplitude b sigma k` with `carryMass b k` forces the unique
exponent `sigma = 1 / 2`.
-/

namespace CarryGeometry

noncomputable section

/-- Local quadratic rigidity at one positive depth. -/
theorem deformedAmplitude_sq_eq_carryMass_iff
    (b k : ℕ) (hb : 1 < b) (hk : 0 < k) (sigma : ℝ) :
    (deformedAmplitude b sigma k) ^ 2 = carryMass b k ↔
      sigma = (1 : ℝ) / 2 := by
  have hb0 : 0 < (b : ℝ) := by
    exact_mod_cast (lt_trans Nat.zero_lt_one hb)
  have hb1 : (b : ℝ) ≠ 1 := by
    exact_mod_cast (ne_of_gt hb)
  have hk0 : 0 < (k : ℝ) := by
    exact_mod_cast hk
  constructor
  · intro hmass
    unfold deformedAmplitude carryMass at hmass
    rw [← Real.rpow_mul_natCast (le_of_lt hb0)
      (-((k : ℝ)) * sigma) 2] at hmass
    have hexponent :
        (-((k : ℝ)) * sigma) * (2 : ℝ) = -((k : ℝ)) :=
      (Real.rpow_right_inj hb0 hb1).mp hmass
    nlinarith
  · intro hsigma
    subst sigma
    rw [deformedAmplitude_half]
    exact carryAmplitude_sq_eq_carryMass b k

/-- Compatibility means reproducing carry mass at every positive depth. -/
def PositionalMassCompatible (b : ℕ) (sigma : ℝ) : Prop :=
  ∀ k : ℕ, 0 < k →
    (deformedAmplitude b sigma k) ^ 2 = carryMass b k

/-- Global positional compatibility selects exactly the critical exponent. -/
theorem positionalMassCompatible_iff
    (b : ℕ) (hb : 1 < b) (sigma : ℝ) :
    PositionalMassCompatible b sigma ↔ sigma = (1 : ℝ) / 2 := by
  constructor
  · intro hcompatible
    exact
      (deformedAmplitude_sq_eq_carryMass_iff
        b 1 hb (by norm_num) sigma).mp
        (hcompatible 1 (by norm_num))
  · intro hsigma
    subst sigma
    intro k hk
    rw [deformedAmplitude_half]
    exact carryAmplitude_sq_eq_carryMass b k

/-- Genuine positional bases have the same compatibility locus. -/
theorem positionalMassCompatible_base_independent
    (b c : ℕ) (hb : 1 < b) (hc : 1 < c) (sigma : ℝ) :
    PositionalMassCompatible b sigma ↔
      PositionalMassCompatible c sigma := by
  rw [positionalMassCompatible_iff b hb sigma,
    positionalMassCompatible_iff c hc sigma]

/-- Depth zero cannot distinguish an exponent. -/
theorem zeroDepth_quadratic_compatible (b : ℕ) (sigma : ℝ) :
    (deformedAmplitude b sigma 0) ^ 2 = carryMass b 0 := by
  simp

/-- Base one cannot distinguish an exponent at any depth. -/
theorem baseOne_quadratic_compatible (k : ℕ) (sigma : ℝ) :
    (deformedAmplitude 1 sigma k) ^ 2 = carryMass 1 k := by
  simp

/-- Consequently, every exponent is globally compatible at base one. -/
theorem positionalMassCompatible_base_one (sigma : ℝ) :
    PositionalMassCompatible 1 sigma := by
  intro k hk
  exact baseOne_quadratic_compatible k sigma

end

end CarryGeometry
