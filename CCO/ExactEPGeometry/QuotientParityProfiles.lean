import CCO.ExactEPGeometry.OriginalRetainedQuotientParityTwo

/-!
# B062 C98–C99: entire quotient parity and connectivity profiles

The pointwise equality of EVERY genuine quotient walk power with the
corresponding E-bisaturated old power commutes with the existential
quantifiers defining the WHOLE even, odd and connected-walk profiles.
These relations include true length zero: quotient even-connectivity
pulls back to the complete E kernel, not old logical equality.

This module is purely relational and adds no homogeneity, SAP, source,
groupoid action section, or exactness premise. The actual source
application is a separate consumer using the same C97 odd pivot.
-/

namespace CCO.ExactEPGeometry

open CCO.ParityHasse.Original

noncomputable section

/-- The full even-walk profile, not merely one chosen stabilized power. -/
theorem quotientEvenWalk_bisaturation_iff
    {X Q : Type*} (pi : X → Q) (E : Setoid X)
    (R : X → X → Prop) (D : Q → Q → Prop)
    (hPowers : ∀ (n : Nat) (a z : X),
      relPow D n (pi a) (pi z) ↔
        setoidBiSaturation E (relPow R n) a z)
    (a z : X) :
    EvenWalk D (pi a) (pi z) ↔
      setoidBiSaturation E (EvenWalk R) a z := by
  constructor
  · rintro ⟨n,he,hPath⟩
    obtain ⟨x,y,hax,hxy,hyz⟩ := (hPowers n a z).mp hPath
    exact ⟨x,y,hax,⟨n,he,hxy⟩,hyz⟩
  · rintro ⟨x,y,hax,⟨n,he,hxy⟩,hyz⟩
    exact ⟨n,he,(hPowers n a z).mpr ⟨x,y,hax,hxy,hyz⟩⟩

/-- The WHOLE odd-walk relation is the E-bisaturation of the old
odd-walk relation, even if an odd profile has no elements. -/
theorem quotientOddWalk_bisaturation_iff
    {X Q : Type*} (pi : X → Q) (E : Setoid X)
    (R : X → X → Prop) (D : Q → Q → Prop)
    (hPowers : ∀ (n : Nat) (a z : X),
      relPow D n (pi a) (pi z) ↔
        setoidBiSaturation E (relPow R n) a z)
    (a z : X) :
    OddWalk D (pi a) (pi z) ↔
      setoidBiSaturation E (OddWalk R) a z := by
  constructor
  · rintro ⟨n,ho,hPath⟩
    obtain ⟨x,y,hax,hxy,hyz⟩ := (hPowers n a z).mp hPath
    exact ⟨x,y,hax,⟨n,ho,hxy⟩,hyz⟩
  · rintro ⟨x,y,hax,⟨n,ho,hxy⟩,hyz⟩
    exact ⟨n,ho,(hPowers n a z).mpr ⟨x,y,hax,hxy,hyz⟩⟩

/-- The complete connectivity profile of arbitrary finite walks,
including zero, is exactly the E-bisaturated old connectivity. -/
theorem quotientConnectedWalk_bisaturation_iff
    {X Q : Type*} (pi : X → Q) (E : Setoid X)
    (R : X → X → Prop) (D : Q → Q → Prop)
    (hPowers : ∀ (n : Nat) (a z : X),
      relPow D n (pi a) (pi z) ↔
        setoidBiSaturation E (relPow R n) a z)
    (a z : X) :
    ConnectedWalk D (pi a) (pi z) ↔
      setoidBiSaturation E (ConnectedWalk R) a z := by
  constructor
  · rintro ⟨n,hPath⟩
    obtain ⟨x,y,hax,hxy,hyz⟩ := (hPowers n a z).mp hPath
    exact ⟨x,y,hax,⟨n,hxy⟩,hyz⟩
  · rintro ⟨x,y,hax,⟨n,hxy⟩,hyz⟩
    exact ⟨n,(hPowers n a z).mpr ⟨x,y,hax,hxy,hyz⟩⟩

end
end CCO.ExactEPGeometry
