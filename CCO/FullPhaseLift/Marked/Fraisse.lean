import CCO.FullPhaseLift.Marked.PairAge
import CCO.OwnerTransversal.CountableAge

/-! The full marked limit is constructed by the existing actual finite
round/union Fraisse construction. Its AP input is a finite CLASS property,
which must be discharged by the chosen-pair full lifting theorem. -/
universe u v w m
namespace CCO.FullPhaseLift.Marked
open scoped FirstOrder
open Canonical APCharacter
noncomputable section
variable {L : Signature} {M : Type m} (U : BoolTable L M)
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable (pack : M ≃ Sigma X) (mask : MaskData S)

/-- Genuine finite-class SAP: full induced legs, same base maps and no
additional collisions. This is a property to PROVE, not a later-stage gate. -/
def StrongAmalgamation : Prop :=
  ∀ (A B C : Chart U S pack mask) (f : A ⟶ B) (g : A ⟶ C),
    ∃ (Z : Chart U S pack mask) (l : B ⟶ Z) (r : C ⟶ Z),
      (∀ x, l.point (f.point x) = r.point (g.point x)) ∧
      ∀ x y, l.point x = r.point y → ∃ a, f.point a = x ∧ g.point a = y

def emptyChart : Chart U S pack mask := by
  let T := pullback U (Fin.elim0 : Fin 0 → M)
  let p : Canonical.Embedding T U := embeddingOf Fin.elim0
    (fun x => Fin.elim0 x) (fun _ _ => rfl)
  exact ⟨⟨0,T,⟨p⟩⟩,Fin.elim0,⟨p,⟨fun x => Fin.elim0 x,fun x => Fin.elim0 x⟩⟩⟩

instance chartNonempty : Nonempty (Chart U S pack mask) := ⟨emptyChart U S pack mask⟩

def emptyEmbedding (C : Chart U S pack mask) : emptyChart U S pack mask ⟶ C := by
  apply embeddingOf Fin.elim0 (fun x => Fin.elim0 x)
  intro r
  refine Fin.cases ?_ (fun s => ?_) r
  · intro xs
    exact Fin.elim0 (xs (0 : Fin 1))
  · intro xs
    change C.old.full s (Fin.elim0 ∘ xs) = U s (Fin.elim0 ∘ xs)
    have h := embedding_read C.realization s (Fin.elim0 ∘ xs)
    have he : C.realization.point ∘ (Fin.elim0 ∘ xs) = Fin.elim0 ∘ xs := by
      funext i
      exact Fin.elim0 (xs i)
    exact h.symm.trans (congrArg (U s) he)

/-- Actual full finite charts supply Mathlib's first-order structures.
The inherited SAP is used only to construct finite AP amalgams. -/
def data (sap : StrongAmalgamation U S pack mask) :
    OwnerTransversal.CountableAge.Data (addBit L).firstOrder where
  Chart := Chart U S pack mask
  Carrier C := Fin C.old.size
  structureCarrier C := toFirstOrder (table C.old.full C.bits)
  hereditary A _ _ C f := by exact hereditary U S pack mask C A f
  joint B C := by
    obtain ⟨Z,l,r,_,_⟩ := sap (emptyChart U S pack mask) B C
      (emptyEmbedding U S pack mask B) (emptyEmbedding U S pack mask C)
    exact ⟨Z,⟨embeddingToFirstOrder l⟩,⟨embeddingToFirstOrder r⟩⟩
  amalgamate A B C f g := by
    obtain ⟨Z,l,r,heq,_⟩ := sap A B C (embeddingOfFirstOrder f) (embeddingOfFirstOrder g)
    refine ⟨Z,embeddingToFirstOrder l,embeddingToFirstOrder r,?_⟩
    letI := toFirstOrder (table A.old.full A.bits)
    letI := toFirstOrder (table Z.old.full Z.bits)
    apply FirstOrder.Language.Embedding.ext
    exact heq

abbrev Limit (sap : StrongAmalgamation U S pack mask) := (data U S pack mask sap).Limit

/-- The homogeneous full realization is an OUTPUT of finite rounds and
actual AP, and is never asserted of a prechosen marking of the old M. -/
theorem limit_homogeneous (sap : StrongAmalgamation U S pack mask) :
    (addBit L).firstOrder.IsUltrahomogeneous (Limit U S pack mask sap) :=
  (data U S pack mask sap).homogeneous

theorem limit_finite_age (sap : StrongAmalgamation U S pack mask)
    (A : Type) [(addBit L).firstOrder.Structure A] [Finite A] :
    Nonempty (A ↪[(addBit L).firstOrder] Limit U S pack mask sap) ↔
      (data U S pack mask sap).InAge A :=
  (data U S pack mask sap).finite_age A

end
end CCO.FullPhaseLift.Marked
