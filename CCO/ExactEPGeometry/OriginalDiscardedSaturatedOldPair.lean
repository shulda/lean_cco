import CCO.ExactEPGeometry.OriginalDiscardedOccupancyQuotientEquiv

/-!
# B062 C103: actual discarded children preserve original E-saturated pair blocks

A discarded full-character SourcePhase reaches EVERY old original-E
class inside EVERY requested real successor child. The child projection
therefore preserves all pair relations obtained by saturating an
original binary relation on BOTH sides by the full original E.

This is a concrete old-binary-colour ingredient for the C103 quotient
source comparison. It does NOT assert that arbitrary new marked
atomic orbitals, complete finite ages, or successor CurrentSources
have already been identified. In particular there is no assumed
quotient SAP, group-action section, pointwise surjectivity or
additional source/provider axiom.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.SourceAge
open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- The actual E;D;E saturation of an arbitrary binary relation D.
This includes equality inside E and makes no atom-realization claim. -/
def setoidSaturation {X : Type u} (S : Setoid X)
    (D : X → X → Prop) (a b : X) : Prop :=
  ∃ x y : X, S.r a x ∧ D x y ∧ S.r y b

/-- Saturation is invariant under changing either representative
inside its entire equivalence class, using only setoid transitivity. -/
theorem setoidSaturation_congr {X : Type u}
    (S : Setoid X) (D : X → X → Prop)
    {a a' b b' : X} (ha : S.r a a') (hb : S.r b b') :
    setoidSaturation S D a b ↔ setoidSaturation S D a' b' := by
  constructor
  · rintro ⟨x,y,hax,hxy,hyb⟩
    exact ⟨x,y,S.trans (S.symm ha) hax,hxy,S.trans hyb hb⟩
  · rintro ⟨x,y,ha'x,hxy,hyb'⟩
    exact ⟨x,y,S.trans ha ha'x,hxy,S.trans hyb' (S.symm hb)⟩

/-- The real ORIGINAL full exact E is a setoid on the whole original
tagged carrier. It is not a separately postulated quotient relation. -/
def originalExactGlobalSetoid
    (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) : Setoid (Sigma A.Point) := by
  let h := originalExactGlobalRelation_equiv A base hOne E
  exact {
    r := originalExactGlobalRelation A base hOne E
    iseqv := ⟨h.refl, h.symm, h.trans⟩
  }

/-- C103, source strength: every original E-class of a real old
current parent meets ANY prescribed legal child of that parent in
the actual discarded SingleStep successor. The proof uses C76's
REAL child-support witness, not a surjective point projection. -/
theorem originalDiscardedEachParentClassHitsChosenChild
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    (E : ExactEq A.source (P.parent r))
    (hNot : ¬ E ≤ PrefixExactLargestLift.largest
      A B P transport tp r (current_kernel_exact_eq B Kroot))
    (c : (SingleStep.successor B phase).Sorts)
    (x : B.Point c.1) :
    ∃ y : (SingleStep.successor B phase).Point c,
      (originalExactGlobalRelation A (P.parent r)
        (fun i => hOne (P.parent r) i) E)
        (P.project ⟨c.1,x⟩)
        ((P.compose (SingleStep.projection B phase)).project ⟨c,y⟩) := by
  let I := SingleStep.identification B phase
  let d : (SingleStep.successor B phase).Sorts :=
    ⟨c.1,UnarySource.tag I c.1 x⟩
  let z : (SingleStep.successor B phase).Point d := ⟨x,rfl⟩
  have hSupport : (originalExactOccupancySetoid
      A B P (P.parent r) (fun i => hOne (P.parent r) i) E).r
      d.1 c.1 :=
    (originalExactOccupancySetoid
      A B P (P.parent r) (fun i => hOne (P.parent r) i) E).refl c.1
  obtain ⟨y,hYZ⟩ :=
    original_discarded_class_hits_every_supported_child
      A B P transport tp hOne Kroot phase E hNot d c hSupport z
  refine ⟨y,?_⟩
  change (originalExactGlobalRelation A (P.parent r)
    (fun i => hOne (P.parent r) i) E)
    ((P.compose (SingleStep.projection B phase)).project ⟨d,z⟩)
    ((P.compose (SingleStep.projection B phase)).project ⟨c,y⟩)
    at hYZ
  change (originalExactGlobalRelation A (P.parent r)
    (fun i => hOne (P.parent r) i) E)
    (P.project ⟨c.1,x⟩)
    ((P.compose (SingleStep.projection B phase)).project ⟨c,y⟩)
  exact hYZ

/-- C103: an arbitrary ORIGINAL binary relation, saturated on both
ends by genuine old E, has exactly its old pair truth value on
representatives chosen inside ANY two prescribed discarded children.
The RHS really constructs two successor points in the same original
classes as the specified old endpoints; no extra nonempty old atomic
trace is assumed. This is the needed pair-block transfer, not yet
the entire quotient orbital language or finite-age equivalence. -/
theorem originalDiscardedSaturatedOldPair_iff
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    (E : ExactEq A.source (P.parent r))
    (hNot : ¬ E ≤ PrefixExactLargestLift.largest
      A B P transport tp r (current_kernel_exact_eq B Kroot))
    (D : Sigma A.Point → Sigma A.Point → Prop)
    (c d : (SingleStep.successor B phase).Sorts)
    (x : B.Point c.1) (y : B.Point d.1) :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let S := originalExactGlobalSetoid A base hBase E
    let PP := P.compose (SingleStep.projection B phase)
    setoidSaturation S D
      (P.project ⟨c.1,x⟩) (P.project ⟨d.1,y⟩) ↔
      ∃ xx : (SingleStep.successor B phase).Point c,
        ∃ yy : (SingleStep.successor B phase).Point d,
          S.r (P.project ⟨c.1,x⟩) (PP.project ⟨c,xx⟩) ∧
          S.r (P.project ⟨d.1,y⟩) (PP.project ⟨d,yy⟩) ∧
          setoidSaturation S D
            (PP.project ⟨c,xx⟩) (PP.project ⟨d,yy⟩) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let S := originalExactGlobalSetoid A base hBase E
  let PP := P.compose (SingleStep.projection B phase)
  change setoidSaturation S D
      (P.project ⟨c.1,x⟩) (P.project ⟨d.1,y⟩) ↔
      ∃ xx : (SingleStep.successor B phase).Point c,
        ∃ yy : (SingleStep.successor B phase).Point d,
          S.r (P.project ⟨c.1,x⟩) (PP.project ⟨c,xx⟩) ∧
          S.r (P.project ⟨d.1,y⟩) (PP.project ⟨d,yy⟩) ∧
          setoidSaturation S D
            (PP.project ⟨c,xx⟩) (PP.project ⟨d,yy⟩)
  constructor
  · intro h
    obtain ⟨xx,hx⟩ :=
      originalDiscardedEachParentClassHitsChosenChild
        A B P transport tp hOne Kroot phase E hNot c x
    obtain ⟨yy,hy⟩ :=
      originalDiscardedEachParentClassHitsChosenChild
        A B P transport tp hOne Kroot phase E hNot d y
    refine ⟨xx,yy,hx,hy,?_⟩
    exact (setoidSaturation_congr S D hx hy).mp h
  · rintro ⟨xx,yy,hx,hy,hD⟩
    exact (setoidSaturation_congr S D hx hy).mpr hD

end
end CCO.ExactEPGeometry
