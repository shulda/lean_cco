import CCO.ExactEPGeometry.NamedSourceIso

/-! Complete named-source isomorphism classes.  The equivalence retains the
whole point set, all realized unary names, and the entire equality-inclusive
pair palette.  It forgets only the arbitrary names of sorts and atoms. -/

universe u v w t
namespace CCO.ExactEPGeometry
open APCharacter.Towers

/-- A genuine complete source isomorphism with equivalent sort names. -/
structure NamedCurrentSourceIso (A B : CurrentSource.{u,v,w,t}) where
  sorts : A.Sorts ≃ B.Sorts
  points : Sigma A.Point ≃ Sigma B.Point
  owner : ∀ p, (points p).1 = sorts p.1
  palette : ∀ p q p' q',
    taggedColour A.source p q = taggedColour A.source p' q' ↔
      taggedColour B.source (points p) (points q) =
        taggedColour B.source (points p') (points q')

namespace NamedCurrentSourceIso

def refl (A : CurrentSource.{u,v,w,t}) : NamedCurrentSourceIso A A where
  sorts := Equiv.refl _
  points := Equiv.refl _
  owner := fun _ => rfl
  palette := fun _ _ _ _ => Iff.rfl

def symm {A B : CurrentSource.{u,v,w,t}}
    (I : NamedCurrentSourceIso A B) : NamedCurrentSourceIso B A where
  sorts := I.sorts.symm
  points := I.points.symm
  owner := by
    intro p
    apply I.sorts.injective
    simpa only [Equiv.apply_symm_apply] using
      (I.owner (I.points.symm p)).symm
  palette := by
    intro p q p' q'
    simpa only [Equiv.apply_symm_apply] using
      (I.palette (I.points.symm p) (I.points.symm q)
        (I.points.symm p') (I.points.symm q')).symm

def trans {A B C : CurrentSource.{u,v,w,t}}
    (I : NamedCurrentSourceIso A B) (J : NamedCurrentSourceIso B C) :
    NamedCurrentSourceIso A C where
  sorts := I.sorts.trans J.sorts
  points := I.points.trans J.points
  owner := fun p => (J.owner (I.points p)).trans (congrArg J.sorts (I.owner p))
  palette := fun p q p' q' =>
    (I.palette p q p' q').trans (J.palette (I.points p) (I.points q)
      (I.points p') (I.points q'))

end NamedCurrentSourceIso

/-- Actual sources modulo complete named-source isomorphism. -/
def namedCurrentSourceSetoid : Setoid CurrentSource.{u,v,w,t} where
  r A B := Nonempty (NamedCurrentSourceIso A B)
  iseqv := {
    refl := fun A => ⟨NamedCurrentSourceIso.refl A⟩
    symm := fun ⟨I⟩ => ⟨I.symm⟩
    trans := fun ⟨I⟩ ⟨J⟩ => ⟨I.trans J⟩ }

abbrev NamedSourceClass := Quotient namedCurrentSourceSetoid.{u,v,w,t}

def namedSourceClass (A : CurrentSource.{u,v,w,t}) : NamedSourceClass.{u,v,w,t} :=
  Quotient.mk namedCurrentSourceSetoid A

theorem namedSourceClass_eq {A B : CurrentSource.{u,v,w,t}}
    (I : NamedCurrentSourceIso A B) : namedSourceClass A = namedSourceClass B :=
  Quotient.sound ⟨I⟩

end CCO.ExactEPGeometry
