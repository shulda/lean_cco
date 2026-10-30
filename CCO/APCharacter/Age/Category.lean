import CCO.APCharacter.Age.Charts
import Mathlib.CategoryTheory.Category.Basic

/-! The actual categories of finite complete marked old diagrams. Morphisms
are full induced embeddings, rather than positive maps or merely functions. -/
universe u v w
namespace CCO.APCharacter.Age
open CategoryTheory
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
noncomputable section

instance chartCategory (M : MaskData S) : SmallCategory (Chart S M) where
  Hom C D := @FirstOrder.Language.Embedding (Language S) (Fin C.size) (Fin D.size)
    C.structure D.structure
  id C := by
    letI := C.structure
    exact FirstOrder.Language.Embedding.refl (Language S) _
  comp {A B C} f g := by
    letI := A.structure
    letI := B.structure
    letI := C.structure
    exact g.comp f
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl

/-- The old age is represented with a dummy constant zero label. This
adds no mathematical structure and keeps the same finite coding language. -/
def zeroMask : MaskData S where
  validBit _ ε := ε = 0
  allowed _ ε η := ε = 0 ∧ η = 0
  reverse _ _ _ := and_comm
  identity _ ε η := by
    constructor
    · rintro ⟨rfl,rfl⟩
      exact ⟨rfl,rfl⟩
    · rintro ⟨rfl,h⟩
      exact ⟨h,h⟩

/-- Constant-zero labels give every actual old finite induced diagram an
object of this ordinary old age, without CCO, AP or source infinitude. -/
def oldChart {V : Type} [Finite V] (point : V → Sigma X)
    (hp : Function.Injective point) : Chart S (zeroMask S) :=
  chartOf S (table S point (fun _ => 0))
    ⟨point,(fun _ => 0),hp,⟨fun _ => rfl,fun _ _ => ⟨rfl,rfl⟩⟩,rfl⟩

end
end CCO.APCharacter.Age
