import CarryGeometry.Mass
import CarryGeometry.Normalization

/-!
# Uniform probability of positional residue classes

At depth `k`, a base-`b` residual space is modeled by `Fin (b ^ k)`.  Every
specified residual class is a singleton, hence has uniform probability
`1 / b ^ k`.  The theorem is parametrized by the class itself: the zero class
is only a canonical representative, not a privileged probabilistic position.
-/

namespace CarryGeometry

noncomputable section

/-- Probability of an event in a finite uniform space. -/
def uniformFiniteProbability {N : ℕ} (event : Finset (Fin N)) : ℝ :=
  (event.card : ℝ) / (N : ℝ)

/-- The event consisting of one specified residual class. -/
def residueClassEvent {N : ℕ} (a : Fin N) : Finset (Fin N) :=
  {a}

/-- A specified residual-class event contains exactly one class. -/
@[simp] theorem card_residueClassEvent {N : ℕ} (a : Fin N) :
    (residueClassEvent a).card = 1 := by
  simp [residueClassEvent]

/-- Every specified class in `Fin (b ^ k)` has probability `carryMass b k`. -/
theorem residueClassEvent_probability
    (b k : ℕ) (a : Fin (b ^ k)) :
    uniformFiniteProbability (residueClassEvent a) = carryMass b k := by
  simp [uniformFiniteProbability, residueClassEvent, carryMass,
    Real.rpow_neg_natCast, Nat.cast_pow, div_eq_mul_inv]

/-- The uniform probability is independent of the chosen residual class. -/
theorem residueClass_probability_independent
    (b k : ℕ) (a d : Fin (b ^ k)) :
    uniformFiniteProbability (residueClassEvent a) =
      uniformFiniteProbability (residueClassEvent d) := by
  rw [residueClassEvent_probability b k a,
    residueClassEvent_probability b k d]

/-- The canonical zero residual class in a nonempty depth space. -/
def canonicalCarryClass (b k : ℕ) (hb : 0 < b) : Fin (b ^ k) :=
  ⟨0, pow_pos hb k⟩

/-- The canonical zero-class carry event. -/
def canonicalCarryEvent (b k : ℕ) (hb : 0 < b) : Finset (Fin (b ^ k)) :=
  residueClassEvent (canonicalCarryClass b k hb)

/-- The canonical carry event has the same mass as every translated class. -/
theorem canonicalCarryEvent_probability
    (b k : ℕ) (hb : 0 < b) :
    uniformFiniteProbability (canonicalCarryEvent b k hb) = carryMass b k := by
  exact residueClassEvent_probability b k (canonicalCarryClass b k hb)

/-! ## The arithmetic carry event -/

/-- The residual class that is saturated immediately before adding one. -/
def incrementCarryClass
    (b k : ℕ) (hb : 0 < b) : Fin (b ^ k) :=
  ⟨b ^ k - 1, Nat.sub_lt (pow_pos hb k) Nat.zero_lt_one⟩

/-- The singleton residual event that produces carry after adding one. -/
def incrementCarryEvent
    (b k : ℕ) (hb : 0 < b) : Finset (Fin (b ^ k)) :=
  residueClassEvent (incrementCarryClass b k hb)

/-- An increment carries exactly when the pre-increment residue is the saturated class. -/
theorem carryAfterIncrementAtDepth_iff_residue_eq_incrementCarryClass
    (b k n : ℕ) (hb : 0 < b) :
    carryAfterIncrementAtDepth b k n ↔
      residueAtDepth b k n = (incrementCarryClass b k hb).val := by
  rw [increment_carries_iff_lowerPositionsSaturated b k n hb,
    lowerPositionsSaturated_iff_residue_eq_last b k n hb]
  rfl

/-- The arithmetic carry-producing class has probability `b⁻ᵏ`. -/
theorem incrementCarryEvent_probability
    (b k : ℕ) (hb : 0 < b) :
    uniformFiniteProbability (incrementCarryEvent b k hb) =
      carryMass b k := by
  exact residueClassEvent_probability b k (incrementCarryClass b k hb)

/-- The carry-producing class and the canonical zero class have equal probability. -/
theorem incrementCarryEvent_probability_eq_canonical
    (b k : ℕ) (hb : 0 < b) :
    uniformFiniteProbability (incrementCarryEvent b k hb) =
      uniformFiniteProbability (canonicalCarryEvent b k hb) := by
  rw [incrementCarryEvent_probability b k hb,
    canonicalCarryEvent_probability b k hb]

end

end CarryGeometry
