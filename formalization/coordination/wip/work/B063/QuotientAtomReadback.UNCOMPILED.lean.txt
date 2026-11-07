import CCO.AutomaticEPCore.QuotientRootCode
import CCO.ExactEPGeometry.OriginalSelectedGlobalEClassEquiv

/-! An actual atom of the initial selected original E-quotient is read
as a complete atom of the literal canonical original quotient. Its full
bipartition is preserved. The SAME fixed root predicate values then read
that atom on the actual original classes of later selected representatives. -/

universe u v w t
namespace CCO.AutomaticEPCore
open CCO.APCharacter CCO.APCharacter.Towers CCO.ExactEPGeometry
open CCO.ParityHasse.Original CCO.RigidGroupoid.Geometry
noncomputable section

/-- True selected quotient points, at any actual prefix, are in bijection
with the literal ORIGINAL E-classes on the fixed original carrier. -/
def selectedOriginalClassEquiv
    (A B : CurrentSource.{u,v,w,t}) (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) :
    Sigma (originalExactSelectedQuotientCurrentSource
      A B P transport base hOne E).Point ≃
      (originalCoreQuotientCurrentSource A base hOne E).Point base :=
  (originalSelectedGlobalEClassEquiv A B P transport base hOne E).trans
    (Quotient.congr (prefixOriginalPointEquiv A B P base hOne)
      (fun _ _ => Iff.rfl))

/-- This equivalence is exactly the actual old E-class of the chosen
selected representative, with the literal original reduct projection. -/
theorem selectedOriginalClassEquiv_apply
    (A B : CurrentSource.{u,v,w,t}) (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (q : Sigma (originalExactSelectedQuotientCurrentSource
      A B P transport base hOne E).Point) :
    selectedOriginalClassEquiv A B P transport base hOne E q =
      Quotient.mk'' (originalPointEquiv A base hOne
        (P.project (originalSelectedTaggedRepresentative A B P transport base hOne E q))) :=
  rfl

private theorem saturation_normalize
    (A : CurrentSource.{u,v,w,t}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i) (E : ExactEq A.source base)
    (p q p' q' : Sigma A.Point) :
    originalCurrentExactSaturatedColour A A (UnaryReduct.identity A.source)
      base hOne E (taggedColour A.source p q) p' q' ↔
    originalCurrentExactSaturatedColour A A (UnaryReduct.identity A.source)
      base hOne E
      ⟨base,base,A.source.colour (originalPointEquiv A base hOne p)
        (originalPointEquiv A base hOne q)⟩
      ⟨base,originalPointEquiv A base hOne p'⟩
      ⟨base,originalPointEquiv A base hOne q'⟩ := by
  rcases p with ⟨i,x⟩
  rcases q with ⟨j,y⟩
  rcases p' with ⟨k,x'⟩
  rcases q' with ⟨l,y'⟩
  cases hOne i
  cases hOne j
  cases hOne k
  cases hOne l
  exact Iff.rfl

/-- The ACTUAL canonical quotient pair colour is the genuine old
E;colour;E block, including the quotient logical diagonal. -/
private theorem canonical_colour_iff_saturation
    (A : CurrentSource.{u,v,w,t}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i) (E : ExactEq A.source base)
    (x y x' y' : A.Point base) :
    (originalCoreQuotient A base hOne E).colour
        (Quotient.mk'' x') (Quotient.mk'' y') =
      (originalCoreQuotient A base hOne E).colour
        (Quotient.mk'' x) (Quotient.mk'' y) ↔
    originalCurrentExactSaturatedColour A A (UnaryReduct.identity A.source)
      base hOne E ⟨base,base,A.source.colour x y⟩ ⟨base,x'⟩ ⟨base,y'⟩ := by
  have block := originalExactAllCurrentPairBlock A A (UnaryReduct.identity A.source)
    (ExactTraceTransport.identity A.source) base hOne E x x' y y'
  apply block.symm.trans
  change Quotient.block A.source
      (originalExactCurrentKernelWords A A (UnaryReduct.identity A.source)
        (ExactTraceTransport.identity A.source) base hOne E)
      (A.source.colour x y) x' y' ↔ _
  unfold originalCurrentExactSaturatedColour
  rw [setoidSaturation_taggedColour_iff]
  have kernel := originalExactCurrentKernelWords_relation
    A A (UnaryReduct.identity A.source) (ExactTraceTransport.identity A.source)
    base hOne E base
  change (∃ v, (∃ u, RawExact.evaluate A.source
      (originalExactCurrentKernelWords A A (UnaryReduct.identity A.source)
        (ExactTraceTransport.identity A.source) base hOne E base).words x' u ∧
      A.source.colour u v = A.source.colour x y) ∧
      RawExact.evaluate A.source
        (originalExactCurrentKernelWords A A (UnaryReduct.identity A.source)
          (ExactTraceTransport.identity A.source) base hOne E base).words v y') ↔ _
  rw [kernel]
  constructor
  · rintro ⟨v,⟨u,hxu,hcol⟩,hvy⟩
    exact ⟨u,v,hxu,hcol,hvy⟩
  · rintro ⟨u,v,hxu,hcol,hvy⟩
    exact ⟨v,⟨u,hxu,hcol⟩,hvy⟩

/-- Equality of the SAME fixed root predicate VALUES, from any actual
selected prefix to another, implies equality of the canonical original
quotient orbital on their true original E-classes. -/
theorem selected_root_code_canonical_colour
    (A B D : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source) (R : UnaryReduct A.source D.source)
    (hP : ExactTraceTransport A.source B.source P)
    (hR : ExactTraceTransport A.source D.source R)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (p q : Sigma (originalExactSelectedQuotientCurrentSource A B P hP base hOne E).Point)
    (s z : Sigma (originalExactSelectedQuotientCurrentSource A D R hR base hOne E).Point)
    (codes : originalQuotientRootCode A D R hR base hOne E s z =
      originalQuotientRootCode A B P hP base hOne E p q) :
    (originalCoreQuotient A base hOne E).colour
        (selectedOriginalClassEquiv A D R hR base hOne E s)
        (selectedOriginalClassEquiv A D R hR base hOne E z) =
      (originalCoreQuotient A base hOne E).colour
        (selectedOriginalClassEquiv A B P hP base hOne E p)
        (selectedOriginalClassEquiv A B P hP base hOne E q) := by
  let repB := originalSelectedTaggedRepresentative A B P hP base hOne E
  let repD := originalSelectedTaggedRepresentative A D R hR base hOne E
  let S := currentOriginalExactSetoid A A (UnaryReduct.identity A.source) base hOne E
  let colour := taggedColour A.source (P.project (repB p)) (P.project (repB q))
  have seed : originalCurrentExactSaturatedColour A A (UnaryReduct.identity A.source)
      base hOne E colour (P.project (repB p)) (P.project (repB q)) :=
    ⟨P.project (repB p),P.project (repB q),S.refl _,rfl,S.refl _⟩
  have atSeed := congrFun codes colour
  have target : originalCurrentExactSaturatedColour A A (UnaryReduct.identity A.source)
      base hOne E colour (R.project (repD s)) (R.project (repD z)) :=
    Eq.mpr atSeed seed
  exact (canonical_colour_iff_saturation A base hOne E _ _ _ _).mpr
    ((saturation_normalize A base hOne E _ _ _ _).mp target)

/-- Genuine initial selected point equivalence with the literal canonical
original quotient. The initial occupancy source has exactly one sort. -/
def initialSelectedQuotientPointEquiv
    (A : CurrentSource.{u,v,w,t}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i) (E : ExactEq A.source base) :
    (originalCodedQuotient A base hOne E (CertifiedGateTower.initial A)).current.Point
        (Quotient.mk'' base) ≃
      (originalCoreQuotientCurrentSource A base hOne E).Point base :=
  (originalPointEquiv
    (originalCodedQuotient A base hOne E (CertifiedGateTower.initial A)).current
    (Quotient.mk'' base) (original_initial_selected_quotient_one_sort A base hOne E)).symm.trans
    (selectedOriginalClassEquiv A A (UnaryReduct.identity A.source)
      (ExactTraceTransport.identity A.source) base hOne E)

/-- This is a FULL actual pair-colour equivalence, not just a match of
some atom names or a relation on a chosen finite diagnostic. -/
theorem initial_selected_quotient_colour_iff_canonical
    (A : CurrentSource.{u,v,w,t}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i) (E : ExactEq A.source base)
    (x y x' y' : (originalCodedQuotient A base hOne E
      (CertifiedGateTower.initial A)).current.Point (Quotient.mk'' base)) :
    (originalCodedQuotient A base hOne E (CertifiedGateTower.initial A)).current.source.colour x' y' =
        (originalCodedQuotient A base hOne E (CertifiedGateTower.initial A)).current.source.colour x y ↔
      (originalCoreQuotient A base hOne E).colour
        (initialSelectedQuotientPointEquiv A base hOne E x')
        (initialSelectedQuotientPointEquiv A base hOne E y') =
      (originalCoreQuotient A base hOne E).colour
        (initialSelectedQuotientPointEquiv A base hOne E x)
        (initialSelectedQuotientPointEquiv A base hOne E y) := by
  have block := originalExactSelectedColour_iff_globalBlock
    A A (UnaryReduct.identity A.source) (ExactTraceTransport.identity A.source)
    base hOne E (Quotient.mk'' base) (Quotient.mk'' base) x x' y y'
  exact block.trans ((saturation_normalize A base hOne E _ _ _ _).trans
    (canonical_colour_iff_saturation A base hOne E _ _ _ _).symm)

end
end CCO.AutomaticEPCore
