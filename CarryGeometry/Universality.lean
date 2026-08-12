import CarryGeometry.Probability
import CarryGeometry.QuadraticAmplitude

/-!
# Foundational positional carry universality

This file consolidates existing scalar laws.  Its main theorem introduces no
new hypothesis or mechanism: it composes uniform singleton probability,
quadratic amplitude--mass identity, local rigidity, and base independence.
-/

namespace CarryGeometry

noncomputable section

/--
Foundational positional carry universality.

For every genuine base, positive depth, and specified residual class:

* the class probability is `carryMass b k`;
* the distinguished amplitude squares to that probability;
* a deformed amplitude squares to it exactly at `sigma = 1 / 2`;
* global positional compatibility has the same locus in every genuine base.
-/
theorem positionalCarryUniversality
    (b k : ℕ) (hb : 1 < b) (hk : 0 < k)
    (a : Fin (b ^ k)) (sigma : ℝ) :
    let classProbability :=
      uniformFiniteProbability (residueClassEvent a)
    classProbability = carryMass b k ∧
      (carryAmplitude b k) ^ 2 = classProbability ∧
      ((deformedAmplitude b sigma k) ^ 2 = classProbability ↔
        sigma = (1 : ℝ) / 2) ∧
      ∀ c : ℕ, 1 < c →
        (PositionalMassCompatible b sigma ↔
          PositionalMassCompatible c sigma) := by
  dsimp only
  have hProbability := residueClassEvent_probability b k a
  refine ⟨hProbability, ?_, ?_, ?_⟩
  · rw [hProbability]
    exact carryAmplitude_sq_eq_carryMass b k
  · rw [hProbability]
    exact deformedAmplitude_sq_eq_carryMass_iff b k hb hk sigma
  · intro c hc
    exact positionalMassCompatible_base_independent b c hb hc sigma

/--
Arithmetic form of foundational universality.

The event is not an abstract chosen singleton: it is the saturated residual
class characterized by the theorem that adding one propagates carry through
the lowest `k` places.
-/
theorem arithmeticCarryUniversality
    (b k : ℕ) (hb : 1 < b) (hk : 0 < k) (sigma : ℝ) :
    let carryProbability :=
      uniformFiniteProbability
        (incrementCarryEvent b k (lt_trans Nat.zero_lt_one hb))
    carryProbability = carryMass b k ∧
      (carryAmplitude b k) ^ 2 = carryProbability ∧
      ((deformedAmplitude b sigma k) ^ 2 = carryProbability ↔
        sigma = (1 : ℝ) / 2) ∧
      ∀ c : ℕ, 1 < c →
        (PositionalMassCompatible b sigma ↔
          PositionalMassCompatible c sigma) := by
  exact positionalCarryUniversality b k hb hk
    (incrementCarryClass b k (lt_trans Nat.zero_lt_one hb)) sigma

end

end CarryGeometry
