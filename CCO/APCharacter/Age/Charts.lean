import CCO.APCharacter.Age.Coding

/-! Actual marked charts, their induced embeddings and ordinary hereditary
closure. Every point map is a literal realization in the original source. -/
universe u v w
open scoped FirstOrder
namespace CCO.APCharacter.Age
open OwnerTransversal.CountableColour
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
noncomputable section
namespace Chart
variable {S} {M : MaskData S}
def point (C : Chart S M) : Fin C.size → Sigma X := C.realized.choose
def bits (C : Chart S M) : Fin C.size → Bit := C.realized.choose_spec.choose
theorem point_injective (C : Chart S M) : Function.Injective C.point :=
  C.realized.choose_spec.choose_spec.1
theorem legal (C : Chart S M) : Legal S M C.point C.bits :=
  C.realized.choose_spec.choose_spec.2.1
theorem table_eq (C : Chart S M) : C.table = Age.table S C.point C.bits :=
  C.realized.choose_spec.choose_spec.2.2

variable (C D : Chart S M)
theorem embedding_names (f : @FirstOrder.Language.Embedding (Language S)
    (Fin C.size) (Fin D.size) C.structure D.structure) :
    (∀ x, (D.point (f x)).1 = (C.point x).1 ∧ D.bits (f x) = C.bits x) ∧
    (∀ x y, taggedColour S (D.point (f x)) (D.point (f y)) =
      taggedColour S (C.point x) (C.point y)) := by
  have h := C.table.embedding_preserves D.table f
  constructor
  · intro x
    have he : ownerEquiv S ((D.point (f x)).1,D.bits (f x)) =
        ownerEquiv S ((C.point x).1,C.bits x) :=
      (congrArg (fun T : Table S (Fin D.size) => T.owner (f x)) D.table_eq).symm.trans
        ((h.1 x).trans (congrArg (fun T : Table S (Fin C.size) => T.owner x) C.table_eq))
    exact ⟨congrArg Prod.fst ((ownerEquiv S).injective he),
      congrArg Prod.snd ((ownerEquiv S).injective he)⟩
  · intro x y
    apply (colourEquiv S).injective
    exact (congrArg (fun T : Table S (Fin D.size) => T.colour (f x) (f y)) D.table_eq).symm.trans
      ((h.2 x y).trans (congrArg (fun T : Table S (Fin C.size) => T.colour x y) C.table_eq))

end Chart

/-- Induced subobjects of actual marked old-age objects are actual marked
old-age objects. This is the full FirstOrder hereditary property. -/
theorem hereditary {M : MaskData S} (C : Chart S M)
    (A : Type) [(Language S).Structure A] [Finite A]
    (f : @FirstOrder.Language.Embedding (Language S) A (Fin C.size) inferInstance C.structure) :
    ∃ D : Chart S M, Nonempty (@FirstOrder.Language.Equiv (Language S) A (Fin D.size) inferInstance D.structure) := by
  letI := C.structure
  let T : Table S A := reindex S C.table f
  have hT : Realized S M T := realized_reindex S C.realized f.toEmbedding
  let D := chartOf S T hT
  have hs : (inferInstance : (Language S).Structure A) = T.toStructure := by
    apply FirstOrder.Language.Structure.ext
    · funext n F
      exact Empty.elim F
    · funext n r x
      apply propext
      cases r with
      | owner b => exact (f.map_rel (Symbol.owner b) x).symm
      | colour c => exact (f.map_rel (Symbol.colour c) x).symm
  have he : Nonempty (@FirstOrder.Language.Equiv (Language S) A (Fin D.size)
      T.toStructure D.structure) := ⟨chartOfEquiv S T hT⟩
  exact ⟨D,cast (congrArg (fun st => Nonempty (@FirstOrder.Language.Equiv
    (Language S) A (Fin D.size) st D.structure)) hs.symm) he⟩

/-- The empty actual old diagram is a marked chart regardless of whether
there is a nonempty old sort. -/
def emptyChart (M : MaskData S) : Chart S M where
  size := 0
  table := table S (fun x => Fin.elim0 x) (fun x => Fin.elim0 x)
  realized := ⟨(fun x => Fin.elim0 x),(fun x => Fin.elim0 x),
    (fun x => Fin.elim0 x),⟨fun x => Fin.elim0 x,fun x => Fin.elim0 x⟩,rfl⟩
instance chartNonempty (M : MaskData S) : Nonempty (Chart S M) := ⟨emptyChart S M⟩

end
end CCO.APCharacter.Age
