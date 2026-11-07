import CCO.CloneTupleGeometry.OwnerSafeTower
import CCO.CloneTupleGeometry.TypedSourceMap
import CCO.ExactEPGeometry.CodedCurrentSource

/-! Literal canonicalization of the SAME genuine owner phase. The pure
clone of its owner successor is the actual B047 marked source, with all
sorts, points and optional colours transported. The original-owner reduct
and clone indices commute pointwise with this isomorphism. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w z
namespace CCO.UnfilteredEP
open CloneTupleGeometry APCharacter APCharacter.Towers
open APCharacter.SourceAge RigidGroupoid.Geometry ExactEPGeometry
noncomputable section

namespace TypedAtomicSourceEquiv
variable {ι : Type u} {X Y : ι → Type v}
variable {S : AtomicSource.{u,v,w} ι X} {T : AtomicSource.{u,v,w} ι Y}

def taggedCodeEquiv (E : CloneTupleGeometry.TypedAtomicSourceEquiv S T) :
    (Σ i, Σ j, Option (S.Atom i j)) ≃ (Σ i, Σ j, Option (T.Atom i j)) where
  toFun := CloneTupleGeometry.TypedAtomicSourceEquiv.taggedCodeMap E
  invFun c := ⟨c.1,c.2.1,c.2.2.map (E.atom c.1 c.2.1).symm⟩
  left_inv c := by
    rcases c with ⟨i,j,c⟩
    apply congrArg (fun d => (⟨i,j,d⟩ : Σ i, Σ j, Option (S.Atom i j)))
    cases c with
    | none => rfl
    | some a => exact congrArg some ((E.atom i j).symm_apply_apply a)
  right_inv c := by
    rcases c with ⟨i,j,c⟩
    apply congrArg (fun d => (⟨i,j,d⟩ : Σ i, Σ j, Option (T.Atom i j)))
    cases c with
    | none => rfl
    | some a => exact congrArg some ((E.atom i j).apply_symm_apply a)
end TypedAtomicSourceEquiv

/-- Clone indices are retained by the actual old-owner reduct. -/
def ownerCloneProject {ι κ : Type u} {X : ι → Type v} {Y : κ → Type v}
    {S : AtomicSource.{u,v,w} ι X} {T : AtomicSource.{u,v,w} κ Y}
    (P : UnaryReduct S T) (p : Sigma (CloneSAP.Carrier Y)) :
    Sigma (CloneSAP.Carrier X) :=
  ⟨P.parent p.1,(P.point p.1 p.2.1,p.2.2)⟩

variable (B : OwnerStage.{u,v,w})
variable {i : B.Sorts} {K : Kernel (CloneSAP.source B.source) i}
variable (phase : SourcePhase B.cloneCurrent.source B.cloneCurrent.homogeneous
  (exactCalculus_of_homogeneous_CCO B.cloneCurrent.source B.cloneCurrent.homogeneous B.cloneCurrent.cco) K)

/-- The displayed canonical child is isomorphic to the SAME specified
B047 successor, not merely to some replacement marked source. -/
def ownerPhaseCanonicalIso :
    NamedCurrentSourceIso (B.successor phase).cloneCurrent
      (SingleStep.successor B.cloneCurrent phase) where
  sorts := Equiv.refl _
  points := CloneTupleGeometry.TypedAtomicSourceEquiv.sigmaPoint
    (actual_marked_owner_clone_source_equiv B.source B.homogeneous B.ap _ phase B.cco
      (B.identification phase))
  owner _ := rfl
  palette p q p' q' := by
    let E := actual_marked_owner_clone_source_equiv B.source B.homogeneous B.ap _ phase B.cco
      (B.identification phase)
    change taggedColour _ p q = taggedColour _ p' q' ↔
      taggedColour _ (CloneTupleGeometry.TypedAtomicSourceEquiv.sigmaPoint E p)
        (CloneTupleGeometry.TypedAtomicSourceEquiv.sigmaPoint E q) =
      taggedColour _ (CloneTupleGeometry.TypedAtomicSourceEquiv.sigmaPoint E p')
        (CloneTupleGeometry.TypedAtomicSourceEquiv.sigmaPoint E q')
    have hpq := CloneTupleGeometry.TypedAtomicSourceEquiv.taggedColour_sigmaPoint E p q
    have hpq' := CloneTupleGeometry.TypedAtomicSourceEquiv.taggedColour_sigmaPoint E p' q'
    constructor
    · intro same
      exact hpq.trans ((congrArg (TypedAtomicSourceEquiv.taggedCodeEquiv E) same).trans hpq'.symm)
    · intro same
      exact (TypedAtomicSourceEquiv.taggedCodeEquiv E).injective
        (hpq.symm.trans (same.trans hpq'))

/-- Actual B047 projection commutes with canonical clone-owner erasure. -/
theorem ownerPhaseCanonicalIso_project (p : Sigma (CloneSAP.Carrier (B.successor phase).Point)) :
    (SingleStep.projection B.cloneCurrent phase).project
      ((ownerPhaseCanonicalIso B phase).points p) =
        ownerCloneProject (B.successorReduct phase) p := by
  rcases p with ⟨c,q,n⟩
  rfl

/-- Actual old binary code, on the actual clone of a displayed owner
stage, with no arbitrary sort or atom reindexing of that original code. -/
def ownerCodedCurrent {A : OwnerStage.{u,v,w}} {Code : Type z}
    (rootCode : Sigma (CloneSAP.Carrier A.Point) → Sigma (CloneSAP.Carrier A.Point) → Code)
    (P : UnaryReduct A.source B.source) :
    CodedCurrentSource.{u,v,w,max u v} Code where
  current := B.cloneCurrent
  code p q := rootCode (ownerCloneProject P p) (ownerCloneProject P q)

/-- The complete canonicalizing isomorphism preserves EVERY fixed old
binary code through the literal projected original points. -/
def ownerPhaseCanonicalCodedIso {A : OwnerStage.{u,v,w}} {Code : Type z}
    (rootCode : Sigma (CloneSAP.Carrier A.Point) → Sigma (CloneSAP.Carrier A.Point) → Code)
    (P : UnaryReduct A.source B.source) :
    CodedCurrentSourceIso
      (ownerCodedCurrent (B.successor phase) rootCode (P.compose (B.successorReduct phase)))
      ((ownerCodedCurrent B rootCode P).successor phase) where
  toNamedCurrentSourceIso := ownerPhaseCanonicalIso B phase
  code_eq p q := by
    change rootCode
      (ownerCloneProject P ((SingleStep.projection B.cloneCurrent phase).project
        ((ownerPhaseCanonicalIso B phase).points p)))
      (ownerCloneProject P ((SingleStep.projection B.cloneCurrent phase).project
        ((ownerPhaseCanonicalIso B phase).points q))) = _
    rw [ownerPhaseCanonicalIso_project,ownerPhaseCanonicalIso_project]
    rfl

end
end CCO.UnfilteredEP
