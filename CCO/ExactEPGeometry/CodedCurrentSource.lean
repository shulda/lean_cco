import CCO.ExactEPGeometry.NamedCurrentSourceIso
import CCO.ExactEPGeometry.CurrentBridgeOldGateBound
import CCO.APCharacter.SourceAge.SingleStep

/-! Source isomorphisms relative to a FIXED binary predicate code. Unlike
plain palette isomorphisms these preserve the VALUE of every original
quotient predicate; renaming those original binary predicates is forbidden. -/

universe u v w t z
namespace CCO.ExactEPGeometry
open APCharacter APCharacter.SourceAge APCharacter.Towers RigidGroupoid.Geometry
open CCO.ParityHasse.Original CCO.ParityHasse.Relative

structure CodedCurrentSource (Code : Type z) where
  current : CurrentSource.{u,v,w,t}
  code : Sigma current.Point → Sigma current.Point → Code

structure CodedCurrentSourceIso {Code : Type z}
    (A B : CodedCurrentSource.{u,v,w,t} Code) extends
    NamedCurrentSourceIso A.current B.current where
  code_eq : ∀ p q, B.code (points p) (points q) = A.code p q

namespace CodedCurrentSourceIso

def refl {Code : Type z} (A : CodedCurrentSource.{u,v,w,t} Code) :
    CodedCurrentSourceIso A A where
  toNamedCurrentSourceIso := NamedCurrentSourceIso.refl A.current
  code_eq := fun _ _ => rfl

def symm {Code : Type z} {A B : CodedCurrentSource.{u,v,w,t} Code}
    (I : CodedCurrentSourceIso A B) : CodedCurrentSourceIso B A where
  toNamedCurrentSourceIso := I.toNamedCurrentSourceIso.symm
  code_eq := by
    intro p q
    change A.code (I.points.symm p) (I.points.symm q) = B.code p q
    simpa only [Equiv.apply_symm_apply] using
      (I.code_eq (I.points.symm p) (I.points.symm q)).symm

def trans {Code : Type z} {A B C : CodedCurrentSource.{u,v,w,t} Code}
    (I : CodedCurrentSourceIso A B) (J : CodedCurrentSourceIso B C) :
    CodedCurrentSourceIso A C where
  toNamedCurrentSourceIso := I.toNamedCurrentSourceIso.trans J.toNamedCurrentSourceIso
  code_eq := fun p q => (J.code_eq (I.points p) (I.points q)).trans (I.code_eq p q)

end CodedCurrentSourceIso

def codedCurrentSourceSetoid (Code : Type z) : Setoid (CodedCurrentSource.{u,v,w,t} Code) where
  r A B := Nonempty (CodedCurrentSourceIso A B)
  iseqv := {
    refl := fun A => ⟨CodedCurrentSourceIso.refl A⟩
    symm := fun ⟨I⟩ => ⟨I.symm⟩
    trans := fun ⟨I⟩ ⟨J⟩ => ⟨I.trans J⟩ }

abbrev CodedSourceClass (Code : Type z) := Quotient (codedCurrentSourceSetoid.{u,v,w,t} Code)

def codedSourceClass {Code : Type z} (A : CodedCurrentSource.{u,v,w,t} Code) :
    CodedSourceClass.{u,v,w,t} Code := Quotient.mk _ A

theorem codedSourceClass_eq {Code : Type z} {A B : CodedCurrentSource.{u,v,w,t} Code}
    (I : CodedCurrentSourceIso A B) : codedSourceClass A = codedSourceClass B :=
  Quotient.sound ⟨I⟩

/-- Lift the SAME fixed original predicate code along the genuine successor
projection. There is no new choice of the original binary language. -/
noncomputable def CodedCurrentSource.successor {Code : Type z}
    (B : CodedCurrentSource.{u,v,w,t} Code)
    {r : B.current.Sorts} {K : Kernel B.current.source r}
    (phase : SourcePhase B.current.source B.current.homogeneous
      (exactCalculus_of_homogeneous_CCO B.current.source B.current.homogeneous B.current.cco) K) :
    CodedCurrentSource.{u,v,w,t} Code where
  current := SingleStep.successor B.current phase
  code := fun p q => B.code ((SingleStep.projection B.current phase).project p)
    ((SingleStep.projection B.current phase).project q)

/-- A true full-character step whose fixed original binary code is retained
literally through its actual unary reduct and through every allowed iso. -/
def CodedSafeSourceStep {Code : Type z}
    (a b : CodedSourceClass.{u,v,w,t} Code) : Prop :=
  ∃ (B : CodedCurrentSource.{u,v,w,t} Code) (r : B.current.Sorts)
    (K : Kernel B.current.source r)
    (phase : SourcePhase B.current.source B.current.homogeneous
      (exactCalculus_of_homogeneous_CCO B.current.source B.current.homogeneous B.current.cco) K),
    codedSourceClass B = a ∧ codedSourceClass (B.successor phase) = b ∧
    ∃ c : B.current.source.Atom r r,
      (∀ x : B.current.Point r, ∀ n : Nat,
        Odd n → ¬relPow (B.current.source.atomRel c) n x x) ∧
      (∀ x : B.current.Point r,
        relativeIndex (evenColourEq B.current.source B.current.homogeneous c).val
          (connectivityColourEq B.current.source B.current.homogeneous c).val x = 2) ∧
      ∃ M : MaximalGate B.current.source B.current.homogeneous
        (evenColourEq B.current.source B.current.homogeneous c)
        (connectivityColourEq B.current.source B.current.homogeneous c),
        M.kernel = (current_kernel_exact_eq B.current K).val

end CCO.ExactEPGeometry
