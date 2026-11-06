import CCO.ExactEPGeometry.OriginalOccupancyOrbitals
import CCO.ExactEPGeometry.OriginalSelectedGlobalEClassEquiv
import CCO.ExactEPGeometry.OriginalCurrentAtomicSaturation

/-!
# B062 C68/C103: actual selected quotient colours as global E-blocks

The REAL selected quotient colour is recognized by full global E-saturation
of the complete current colour of its selected representatives. The endpoint
occupancy names remain fixed. Changing the representatives of the SEED pair
inside their true global E-classes changes no full block, even when their
named current parents differ. This uses actual pair homogeneity, never an
equivariant choice of representatives or a quotient automorphism section.
-/

universe u v w t
namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- Full atomic blocks depend on the two true global E-classes of their
realized seed, including seeds at different current named parents. -/
theorem originalCurrentExactAtomicBlock_seed_congr
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (a b a' b' p q : Sigma B.Point)
    (ha : (currentOriginalExactSetoid A B P base hOne E).r a a')
    (hb : (currentOriginalExactSetoid A B P base hOne E).r b b') :
    originalCurrentExactSaturatedColour A B P base hOne E
      (taggedColour B.source a b) p q ↔
    originalCurrentExactSaturatedColour A B P base hOne E
      (taggedColour B.source a' b') p q := by
  let S := currentOriginalExactSetoid A B P base hOne E
  have transfer (a b a' b' : Sigma B.Point)
      (hSeed : originalCurrentExactSaturatedColour A B P base hOne E
        (taggedColour B.source a b) a' b')
      (h : originalCurrentExactSaturatedColour A B P base hOne E
        (taggedColour B.source a' b') p q) :
      originalCurrentExactSaturatedColour A B P base hOne E
        (taggedColour B.source a b) p q := by
    obtain ⟨x,y,hpx,hColour,hyq⟩ := h
    have hxy := (originalCurrentExactSaturatedColour_taggedColour_iff
      A B P base hOne E (taggedColour B.source a b)
      a' b' x y hColour.symm).mp hSeed
    exact (setoidSaturation_congr S
      (fun x y => taggedColour B.source x y = taggedColour B.source a b)
      hpx (S.symm hyq)).mpr hxy
  constructor
  · intro h
    exact transfer a' b' a b ⟨a',b',ha,rfl,S.symm hb⟩ h
  · intro h
    exact transfer a b a' b' ⟨a,b,S.symm ha,rfl,hb⟩ h

/-- On two ACTUAL selected occupancy parents, quotient colour equality
is exactly membership in the full global original-E atomic block. The
local kernel words are discharged by their proved current E-restriction. -/
theorem originalExactSelectedPairColour_iff_globalBlock
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (c d : OriginalOccupancy A B P base hOne E)
    (x a : B.Point (originalOccupancyRepresentative A B P base hOne E c))
    (y b : B.Point (originalOccupancyRepresentative A B P base hOne E d)) :
    let Q := originalExactSelectedQuotientCurrentSource A B P transport base hOne E
    Q.source.colour (Quotient.mk'' a : Q.Point c) (Quotient.mk'' b : Q.Point d) =
      Q.source.colour (Quotient.mk'' x : Q.Point c) (Quotient.mk'' y : Q.Point d) ↔
    originalCurrentExactSaturatedColour A B P base hOne E
      (taggedColour B.source ⟨originalOccupancyRepresentative A B P base hOne E c,x⟩
        ⟨originalOccupancyRepresentative A B P base hOne E d,y⟩)
      ⟨originalOccupancyRepresentative A B P base hOne E c,a⟩
      ⟨originalOccupancyRepresentative A B P base hOne E d,b⟩ := by
  let i := originalOccupancyRepresentative A B P base hOne E c
  let j := originalOccupancyRepresentative A B P base hOne E d
  let S := currentOriginalExactSetoid A B P base hOne E
  have hBlock := originalExactSelectedPairBlock
    A B P transport base hOne E c d x a y b
  change _ ↔ originalCurrentExactSaturatedColour A B P base hOne E
    ⟨i,j,B.source.colour x y⟩ ⟨i,a⟩ ⟨j,b⟩
  refine hBlock.symm.trans ?_
  change Quotient.block B.source
      (originalExactCurrentKernelWords A B P transport base hOne E)
      (B.source.colour x y) a b ↔
    setoidSaturation S (fun u v => taggedColour B.source u v =
      ⟨i,j,B.source.colour x y⟩) ⟨i,a⟩ ⟨j,b⟩
  rw [setoidSaturation_taggedColour_iff]
  have hi := originalExactCurrentKernelWords_relation A B P transport base hOne E i
  have hj := originalExactCurrentKernelWords_relation A B P transport base hOne E j
  change (∃ v, (∃ u, RawExact.evaluate B.source
      (originalExactCurrentKernelWords A B P transport base hOne E i).words a u ∧
      B.source.colour u v = B.source.colour x y) ∧
      RawExact.evaluate B.source
        (originalExactCurrentKernelWords A B P transport base hOne E j).words v b) ↔ _
  rw [hi,hj]
  constructor
  · rintro ⟨v,⟨u,hau,hColour⟩,hvb⟩
    exact ⟨u,v,(originalExactOnCurrentSort_iff
      A B P transport base hOne E i a u).mp hau,hColour,
      (originalExactOnCurrentSort_iff A B P transport base hOne E j v b).mp hvb⟩
  · rintro ⟨u,v,hau,hColour,hvb⟩
    exact ⟨v,⟨u,(originalExactOnCurrentSort_iff
      A B P transport base hOne E i a u).mpr hau,hColour⟩,
      (originalExactOnCurrentSort_iff A B P transport base hOne E j v b).mpr hvb⟩

/-- The same full palette description on every true selected quotient
point, with its canonical representative and original occupancy name. -/
theorem originalExactSelectedColour_iff_globalBlock
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (c d : OriginalOccupancy A B P base hOne E)
    (q q' : (originalExactSelectedQuotientCurrentSource
      A B P transport base hOne E).Point c)
    (s s' : (originalExactSelectedQuotientCurrentSource
      A B P transport base hOne E).Point d) :
    let Q := originalExactSelectedQuotientCurrentSource A B P transport base hOne E
    let rep := originalSelectedTaggedRepresentative A B P transport base hOne E
    Q.source.colour q' s' = Q.source.colour q s ↔
      originalCurrentExactSaturatedColour A B P base hOne E
        (taggedColour B.source (rep ⟨c,q⟩) (rep ⟨d,s⟩))
        (rep ⟨c,q'⟩) (rep ⟨d,s'⟩) := by
  have h := originalExactSelectedPairColour_iff_globalBlock
    A B P transport base hOne E c d
      (Quotient.out q) (Quotient.out q') (Quotient.out s) (Quotient.out s')
  dsimp only at h
  have hq := originalSelectedTaggedRepresentative_class A B P transport base hOne E ⟨c,q⟩
  have hq' := originalSelectedTaggedRepresentative_class A B P transport base hOne E ⟨c,q'⟩
  have hs := originalSelectedTaggedRepresentative_class A B P transport base hOne E ⟨d,s⟩
  have hs' := originalSelectedTaggedRepresentative_class A B P transport base hOne E ⟨d,s'⟩
  change (Quotient.mk'' (Quotient.out q) :
    (originalExactSelectedQuotientCurrentSource A B P transport base hOne E).Point c) = q at hq
  change (Quotient.mk'' (Quotient.out q') :
    (originalExactSelectedQuotientCurrentSource A B P transport base hOne E).Point c) = q' at hq'
  change (Quotient.mk'' (Quotient.out s) :
    (originalExactSelectedQuotientCurrentSource A B P transport base hOne E).Point d) = s at hs
  change (Quotient.mk'' (Quotient.out s') :
    (originalExactSelectedQuotientCurrentSource A B P transport base hOne E).Point d) = s' at hs'
  erw [hq,hq',hs,hs'] at h
  exact h

/-- The COMPLETE tagged quotient pair colour retains both occupancy
names and the full global E-block; neither unary condition is omitted. -/
theorem originalExactSelectedTaggedColour_iff_globalBlock
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (q s q' s' : Sigma (originalExactSelectedQuotientCurrentSource
      A B P transport base hOne E).Point) :
    let Q := originalExactSelectedQuotientCurrentSource A B P transport base hOne E
    let rep := originalSelectedTaggedRepresentative A B P transport base hOne E
    taggedColour Q.source q' s' = taggedColour Q.source q s ↔
      q'.1 = q.1 ∧ s'.1 = s.1 ∧
      originalCurrentExactSaturatedColour A B P base hOne E
        (taggedColour B.source (rep q) (rep s)) (rep q') (rep s') := by
  dsimp only
  rcases q with ⟨c,q⟩
  rcases s with ⟨d,s⟩
  rcases q' with ⟨c',q'⟩
  rcases s' with ⟨d',s'⟩
  constructor
  · intro h
    have hc : c' = c := congrArg Sigma.fst h
    have hd : d' = d := congrArg (fun a => a.2.1) h
    subst c'
    subst d'
    refine ⟨rfl,rfl,?_⟩
    have hColour := eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
    exact (originalExactSelectedColour_iff_globalBlock
      A B P transport base hOne E c d q q' s s').mp hColour
  · rintro ⟨hc,hd,hBlock⟩
    change c' = c at hc
    change d' = d at hd
    subst c'
    subst d'
    have hColour := (originalExactSelectedColour_iff_globalBlock
      A B P transport base hOne E c d q q' s s').mpr hBlock
    exact congrArg (fun a => (⟨c,d,a⟩ : Age.Colour
      (originalExactSelectedQuotientCurrentSource A B P transport base hOne E).source)) hColour

end
end CCO.ExactEPGeometry
