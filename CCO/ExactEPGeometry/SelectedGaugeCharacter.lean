import CCO.RigidGroupoid.Phase.AbstractCharacter

/-!
# B062 C84: actual ZMod 2 character normalization across object names

The source's complete rigid groupoid character is additive on every
whole Arrow. Under identification of duplicate original E-occupancy
sort names, correcting by the two endpoint offsets must preserve
identities and ALL compositions. These elementary statements hold for
every category and every objectwise offset. The actual B062 application
must derive the offsets and the identity-bridge equation from the real
old-gate arrows of C79 rather than postulate a quotient phase.
-/

universe u v

namespace CCO.ExactEPGeometry

open CategoryTheory
open CCO.RigidGroupoid.Phase

noncomputable section

/-- The full ZMod 2 objectwise correction is a genuine character.
No selected generator, extra groupoid action, or SAP is assumed. -/
def gaugeCharacter {J : Type u} [Category.{v} J]
    (chi : Abstract.Character J) (gamma : J → ZMod 2) :
    Abstract.Character J where
  value := fun {a b} R => gamma a + chi.value R + gamma b
  map_id := by
    intro a
    change gamma a + chi.value (𝟙 a) + gamma a = 0
    rw [chi.map_id]
    have hDouble : ∀ z : ZMod 2, z + z = 0 := by decide
    simpa only [add_zero] using hDouble (gamma a)
  map_comp := by
    intro a b c R T
    change gamma a + chi.value (R ≫ T) + gamma c =
      (gamma a + chi.value R + gamma b) +
      (gamma b + chi.value T + gamma c)
    rw [chi.map_comp]
    have hDouble : gamma b + gamma b = 0 := by
      have hh : ∀ z : ZMod 2, z + z = 0 := by decide
      exact hh _
    calc
      gamma a + (chi.value R + chi.value T) + gamma c =
          (gamma a + (chi.value R + chi.value T) + gamma c) + 0 :=
        (add_zero _).symm
      _ = (gamma a + (chi.value R + chi.value T) + gamma c) +
            (gamma b + gamma b) := by rw [hDouble]
      _ = (gamma a + chi.value R + gamma b) +
            (gamma b + chi.value T + gamma c) := by abel

/-- A real identity bridge whose original phase is precisely the sum
of its canonical endpoint offsets becomes zero under normalization.
This algebraic result will be instantiated using the actual C79
bridge cocycle on each supported original E-occupancy component. -/
theorem gaugeCharacter_bridge_zero {J : Type u} [Category.{v} J]
    (chi : Abstract.Character J) (gamma : J → ZMod 2)
    {a b : J} (R : a ⟶ b)
    (hR : chi.value R = gamma a + gamma b) :
    (gaugeCharacter chi gamma).value R = 0 := by
  change gamma a + chi.value R + gamma b = 0
  rw [hR]
  have ha : gamma a + gamma a = 0 := by
    have hh : ∀ z : ZMod 2, z + z = 0 := by decide
    exact hh _
  have hb : gamma b + gamma b = 0 := by
    have hh : ∀ z : ZMod 2, z + z = 0 := by decide
    exact hh _
  calc
    gamma a + (gamma a + gamma b) + gamma b =
        (gamma a + gamma a) + (gamma b + gamma b) := by abel
    _ = 0 := by rw [ha,hb]; exact zero_add 0

end
end CCO.ExactEPGeometry
