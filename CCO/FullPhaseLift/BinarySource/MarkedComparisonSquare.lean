import CCO.FullPhaseLift.Marked.PairAge
import CCO.APCharacter.Age.Category

/-! The finite full/pair forgetful square uses literally the SAME finite
vertex maps. Auxiliary full realizations may differ, but actual canonical
pair faithfulness makes both old pair objects equal as complete charts. -/

open scoped FirstOrder
universe u v w m
namespace CCO.FullPhaseLift.BinarySource.MarkedComparison
open Canonical APCharacter CategoryTheory
noncomputable section
variable {L : Signature} {M : Type m} (U : BoolTable L M)
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable (pack : M ≃ Sigma X) (mask : MaskData S) (names : Marked.PairFaithful U S pack)

def oldPairObject (C : Marked.OldChart U) : Age.Chart S (Age.zeroMask S) where
  size := C.size
  table := Age.table S (pack ∘ C.realized.some.point) (fun _ => 0)
  realized := ⟨pack ∘ C.realized.some.point,fun _ => 0,
    pack.injective.comp C.realized.some.injective,
    ⟨fun _ => rfl,fun _ _ => ⟨rfl,rfl⟩⟩,rfl⟩

def oldPairMap {A B : Marked.OldChart U} (f : A ⟶ B) :
    @FirstOrder.Language.Embedding (Age.Language S) (Fin A.size) (Fin B.size)
      (oldPairObject U S pack A).structure (oldPairObject U S pack B).structure := by
  have hc (x y : Fin A.size) :
      taggedColour S (pack (B.realized.some.point (f.point x)))
        (pack (B.realized.some.point (f.point y))) =
      taggedColour S (pack (A.realized.some.point x)) (pack (A.realized.some.point y)) :=
    names A.realized.some (B.realized.some.comp f) x y
  exact (oldPairObject U S pack A).table.embedding (oldPairObject U S pack B).table
    ⟨f.point,f.injective⟩
    (fun x => congrArg (Age.ownerEquiv S)
      (Prod.ext (congrArg (fun c : Age.Colour S => c.1) (hc x x)) rfl))
    (fun x y => congrArg (Age.colourEquiv S) (hc x y))

def erasedPairObject (C : Age.Chart S mask) : Age.Chart S (Age.zeroMask S) where
  size := C.size
  table := Age.table S C.point (fun _ => 0)
  realized := ⟨C.point,fun _ => 0,C.point_injective,
    ⟨fun _ => rfl,fun _ _ => ⟨rfl,rfl⟩⟩,rfl⟩

def erasedPairMap {A B : Age.Chart S mask}
    (f : @FirstOrder.Language.Embedding (Age.Language S) (Fin A.size) (Fin B.size) A.structure B.structure) :
    @FirstOrder.Language.Embedding (Age.Language S) (Fin A.size) (Fin B.size)
      (erasedPairObject S mask A).structure (erasedPairObject S mask B).structure := by
  letI := A.structure
  letI := B.structure
  have hn := A.embedding_names B f
  exact (erasedPairObject S mask A).table.embedding (erasedPairObject S mask B).table
    f.toEmbedding
    (fun x => congrArg (Age.ownerEquiv S) (Prod.ext (hn.1 x).1 rfl))
    (fun x y => congrArg (Age.colourEquiv S) (hn.2 x y))

private theorem chart_ext {A B : Age.Chart S (Age.zeroMask S)}
    (hs : A.size = B.size) (ht : HEq A.table B.table) : A = B := by
  cases A
  cases B
  cases hs
  cases eq_of_heq ht
  rfl

include names in
theorem forgetful_square_object (A : Marked.Chart U S pack mask) :
    oldPairObject U S pack A.old = erasedPairObject S mask (Marked.pairChart U S pack mask A) := by
  let C := Marked.pairChart U S pack mask A
  letI := C.structure
  have h := Marked.pairEmbedding_names U S pack mask (A := A) (Z := C) (𝟙 C)
  have hc (x y : Fin A.old.size) :
      taggedColour S (C.point x) (C.point y) =
        taggedColour S (pack (A.old.realized.some.point x)) (pack (A.old.realized.some.point y)) :=
    (h.2 x y).trans (names A.old.realized.some A.realization x y)
  apply chart_ext S (A := oldPairObject U S pack A.old)
    (B := erasedPairObject S mask (Marked.pairChart U S pack mask A)) rfl
  apply heq_of_eq
  apply congrArg₂ OwnerTransversal.CountableColour.Table.mk
  · funext x
    exact congrArg (Age.ownerEquiv S)
      (Prod.ext (congrArg (fun c : Age.Colour S => c.1) (hc x x)).symm rfl)
  · funext x y
    exact congrArg (Age.colourEquiv S) (hc x y).symm

/-- Both routes around the full/pair square are the exact original finite
embedding map, even though their structure-preservation proofs differ. -/
theorem forgetful_square_map {A B : Marked.Chart U S pack mask} (f : A ⟶ B)
    (x : Fin A.old.size) :
    (oldPairMap U S pack names (Marked.oldEmbedding f)).toFun x =
      (erasedPairMap S mask (A := Marked.pairChart U S pack mask A)
        (B := Marked.pairChart U S pack mask B) (Marked.pairEmbedding U S pack mask names f)).toFun x := rfl

end
end CCO.FullPhaseLift.BinarySource.MarkedComparison
