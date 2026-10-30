import CCO.APCharacter.Age.Image

/-! Genuine ordinary AP for the actual marked finite class, constructed
from the finite marked-completion theorem. This generic consumer is later
instantiated by the maximal exact character masks and their proved calculus. -/
universe u v w t
namespace CCO.APCharacter.Age
open OwnerTransversal.CountableColour
open scoped FirstOrder
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
noncomputable section

def CompletionProperty (M : MaskData S) : Prop :=
  ∀ {V : Type} (D : PartialDiagram S V) (bits : V → Bit),
    M.LocalLegal D bits → (∀ K : SimpleCycle D, CycleHom K) →
    ∃ F : DiagramHom D, ∃ mark, M.GlobalMarking mark ∧
      ∀ x, mark (F.image x) = bits x

variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) {M : MaskData S}
include H

/-- AP permits extra cross-leg identifications, while each displayed
complete leg remains induced and injective. -/
theorem amalgamate (completion : CompletionProperty S M) (A B C : Chart S M)
    (f : @FirstOrder.Language.Embedding (Language S) (Fin A.size) (Fin B.size) A.structure B.structure)
    (g : @FirstOrder.Language.Embedding (Language S) (Fin A.size) (Fin C.size) A.structure C.structure) :
    ∃ Z : Chart S M,
      ∃ f' : @FirstOrder.Language.Embedding (Language S) (Fin B.size) (Fin Z.size) B.structure Z.structure,
      ∃ g' : @FirstOrder.Language.Embedding (Language S) (Fin C.size) (Fin Z.size) C.structure Z.structure,
      ∀ x, f'.toFun (f.toFun x) = g'.toFun (g.toFun x) := by
  classical
  letI := A.structure
  letI := B.structure
  letI := C.structure
  obtain ⟨h,hh⟩ := align_span S H A B C f g
  let p := B.point
  let q := fun x => h • C.point x
  let fl := f.toEmbedding
  let gr := g.toEmbedding
  have ha : ∀ a, p (fl a) = q (gr a) := fun a => (hh a).symm
  have hb : ∀ a, B.bits (fl a) = C.bits (gr a) := fun a =>
    ((A.embedding_names B f).1 a).2.trans ((A.embedding_names C g).1 a).2.symm
  let D := Span.diagram (S := S) fl gr p q
  let bits := Span.bits fl gr B.bits C.bits
  have legal : M.LocalLegal D bits := Span.localLegal fl gr p q B.bits C.bits M
    B.legal (legal_translate S H C.legal h) ha hb
  obtain ⟨F,mark,hm,he⟩ := completion D bits legal (Span.cycle_feasible fl gr p q)
  letI := D.finite_type
  let Q := FiniteImage.Carrier F
  let T := FiniteImage.table F mark
  have hT : Realized S M T := FiniteImage.realized F mark hm
  let Z := chartOf S T hT
  have completeL : ∀ x y (hn : x ≠ y),
      ∃ a, D.edge (Span.left fl gr x) (Span.left fl gr y) ((Span.left fl gr).injective.ne hn) = some a :=
    Span.leg_complete fl gr p q (Span.left fl gr) p B.point_injective
      (fun _ => rfl) (fun x y => Or.inl ⟨x,y,rfl,rfl⟩)
  have completeR : ∀ x y (hn : x ≠ y),
      ∃ a, D.edge (Span.right fl gr x) (Span.right fl gr y) ((Span.right fl gr).injective.ne hn) = some a :=
    Span.leg_complete fl gr p q (Span.right fl gr) q
      ((MulAction.injective h).comp C.point_injective)
      (Span.point_right fl gr p q ha) (fun x y => Or.inr ⟨x,y,rfl,rfl⟩)
  let old := Span.oldHom (S := S) fl gr p q
  have ownerL : ∀ x, B.table.owner x = ownerEquiv S
      (D.vertexSort (Span.left fl gr x),bits (Span.left fl gr x)) := by
    intro x
    exact congrArg (fun T : Table S (Fin B.size) => T.owner x) B.table_eq
  have colourL : ∀ x y, B.table.colour x y = colourEquiv S
      (taggedColour S (old.image (Span.left fl gr x)) (old.image (Span.left fl gr y))) := by
    intro x y
    exact congrArg (fun T : Table S (Fin B.size) => T.colour x y) B.table_eq
  have ownerR : ∀ x, C.table.owner x = ownerEquiv S
      (D.vertexSort (Span.right fl gr x),bits (Span.right fl gr x)) := by
    intro x
    have hc := congrArg (fun T : Table S (Fin C.size) => T.owner x) C.table_eq
    apply hc.trans
    apply congrArg (ownerEquiv S)
    apply Prod.ext
    · change (C.point x).1 = (Span.point fl gr p q (Span.right fl gr x)).1
      rw [Span.point_right fl gr p q ha]
      exact (H.preserves_sort h (C.point x)).symm
    · exact (Span.bits_right fl gr B.bits C.bits hb x).symm
  have colourR : ∀ x y, C.table.colour x y = colourEquiv S
      (taggedColour S (old.image (Span.right fl gr x)) (old.image (Span.right fl gr y))) := by
    intro x y
    have hc := congrArg (fun T : Table S (Fin C.size) => T.colour x y) C.table_eq
    apply hc.trans
    apply congrArg (colourEquiv S)
    change taggedColour S (C.point x) (C.point y) =
      taggedColour S (Span.point fl gr p q (Span.right fl gr x))
        (Span.point fl gr p q (Span.right fl gr y))
    rw [Span.point_right fl gr p q ha,Span.point_right fl gr p q ha]
    exact (H.preserves_colours h _ _).symm
  let eL := FiniteImage.embedding F B.table (Span.left fl gr) completeL old bits mark he ownerL colourL
  let eR := FiniteImage.embedding F C.table (Span.right fl gr) completeR old bits mark he ownerR colourR
  letI := T.toStructure
  letI := Z.structure
  let iso := chartOfEquiv S T hT
  refine ⟨Z,iso.toEmbedding.comp eL,iso.toEmbedding.comp eR,?_⟩
  intro x
  change iso (Quotient.mk _ (Span.left fl gr (f x))) =
    iso (Quotient.mk _ (Span.right fl gr (g x)))
  exact congrArg iso (congrArg (Quotient.mk _) (Span.commute fl gr x))

end
end CCO.APCharacter.Age
