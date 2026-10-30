import CCO.FullPhaseLift.Marked.Hereditary

/-! The full marked pair age is EXACTLY the actual chosen pair age.
All objects here have actual injective pair realizations; arbitrary
triangle-consistent tables are not substituted for age membership. -/
universe u v w m
namespace CCO.FullPhaseLift.Marked
open Canonical APCharacter
noncomputable section
variable {L : Signature} {M : Type m} (U : BoolTable L M)
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable (pack : M ≃ Sigma X) (mask : MaskData S)

namespace Chart
variable {U S pack mask}
def realization (C : Chart U S pack mask) : Canonical.Embedding C.old.full U := C.legal.choose

def pairPoint (C : Chart U S pack mask) : Fin C.old.size → Sigma X :=
  pack ∘ C.realization.point

theorem pairPoint_injective (C : Chart U S pack mask) : Function.Injective C.pairPoint :=
  pack.injective.comp C.realization.injective

theorem pairLegal (C : Chart U S pack mask) : Age.Legal S mask C.pairPoint C.bits :=
  C.legal.choose_spec
end Chart

/-- Forget all higher old tuples, retaining the actual chosen pair table
and the SAME vertex bits. Its full source object remains available. -/
def pairChart (C : Chart U S pack mask) : Age.Chart S mask where
  size := C.old.size
  table := Age.table S C.pairPoint C.bits
  realized := ⟨C.pairPoint,C.bits,C.pairPoint_injective,C.pairLegal,rfl⟩

/-- A pair-age object has a full lift on precisely its original vertices:
take the old FULL induced structure of its actual pair realization. -/
def fullChartOfPair (C : Age.Chart S mask) : Chart U S pack mask := by
  let p : Canonical.Embedding (pullback U (pack.symm ∘ C.point)) U :=
    embeddingOf (pack.symm ∘ C.point) (pack.symm.injective.comp C.point_injective)
      (fun _ _ => rfl)
  have hp : Age.Legal S mask (pack ∘ p.point) C.bits := by
    have he : pack ∘ p.point = C.point := funext (fun x => pack.apply_symm_apply _)
    rw [he]
    exact C.legal
  exact ⟨⟨C.size,pullback U (pack.symm ∘ C.point),⟨p⟩⟩,C.bits,⟨p,hp⟩⟩

private theorem pairChart_ext {A B : Age.Chart S mask} (hsize : A.size = B.size)
    (htable : HEq A.table B.table) : A = B := by
  cases A
  cases B
  cases hsize
  cases eq_of_heq htable
  rfl

/-- Canonical full realization choices cannot change a pair table. -/
theorem pairChart_fullChartOfPair (names : PairFaithful U S pack) (C : Age.Chart S mask) :
    pairChart U S pack mask (fullChartOfPair U S pack mask C) = C := by
  let A := fullChartOfPair U S pack mask C
  let p : Canonical.Embedding (pullback U (pack.symm ∘ C.point)) U :=
    embeddingOf (pack.symm ∘ C.point) (pack.symm.injective.comp C.point_injective)
      (fun _ _ => rfl)
  have hc (x y : Fin C.size) :
      taggedColour S (A.pairPoint x) (A.pairPoint y) =
        taggedColour S (C.point x) (C.point y) := by
    have h := names p A.realization x y
    simpa only [p,Canonical.embeddingOf,Chart.pairPoint,Function.comp_def,pack.apply_symm_apply] using h
  apply pairChart_ext (S := S) (mask := mask)
    (A := pairChart U S pack mask (fullChartOfPair U S pack mask C)) (B := C) rfl
  apply heq_of_eq
  change Age.table S A.pairPoint C.bits = C.table
  rw [C.table_eq]
  apply congrArg₂ OwnerTransversal.CountableColour.Table.mk
  · funext x
    exact congrArg (fun i => Age.ownerEquiv S (i,C.bits x))
      (congrArg (fun c : Age.Colour S => c.1) (hc x x))
  · funext x y
    exact congrArg (Age.colourEquiv S) (hc x y)

/-- Both pair-age inclusions, on actual identical finite pair objects. -/
theorem pairChart_surjective (names : PairFaithful U S pack) :
    Function.Surjective (pairChart U S pack mask) :=
  fun C => ⟨fullChartOfPair U S pack mask C,pairChart_fullChartOfPair U S pack mask names C⟩

end
end CCO.FullPhaseLift.Marked
