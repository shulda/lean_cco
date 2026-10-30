import CCO.APCharacter.Completion.FiniteProcedure

/-! Universe-small finite charts use the SAME completion procedure by literal
ULift reindexing. No countability, infinitude or fresh-point premise is added. -/
universe u v w t
namespace CCO.APCharacter.Completion
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {V : Type} (D : PartialDiagram S V)

noncomputable def liftDiagram : PartialDiagram S (ULift.{max u v} V) where
  finite_type := by letI := D.finite_type; infer_instance
  vertexSort a := D.vertexSort a.down
  edge a b hab := D.edge a.down b.down (fun h => hab (ULift.ext _ _ h))
  edge_reverse a b hab c := D.edge_reverse a.down b.down _ c

def lowerLiftCycle (C : SimpleCycle (liftDiagram D)) : SimpleCycle D where
  length := C.length
  length_ge_three := C.length_ge_three
  length_pos := C.length_pos
  vertices := ⟨fun p => (C.vertices p).down,by
    intro p q h
    exact C.vertices.injective (ULift.ext _ _ h)⟩
  next_ne p := by
    intro h
    exact C.next_ne p (ULift.ext _ _ h)
  specified p := C.specified p

/-- Every actual lifted simple cycle is literally the same old finite cycle
on its down-projected vertices; all edge names and point witnesses persist. -/
theorem liftDiagram_cycles (cycles : ∀ C : SimpleCycle D, CycleHom C) :
    ∀ C : SimpleCycle (liftDiagram D), CycleHom C := by
  intro C
  exact cycles (lowerLiftCycle D C)

def lowerLiftHom (f : DiagramHom (liftDiagram D)) : DiagramHom D where
  point a := f.point (ULift.up a)
  preserves_edge a b hab c hc :=
    f.preserves_edge (ULift.up a) (ULift.up b) (fun h => hab (congrArg ULift.down h)) c hc

variable (M : MaskData S) (bits : V → Bit)

theorem liftDiagram_legal (legal : M.LocalLegal D bits) :
    M.LocalLegal (liftDiagram D) (fun a => bits a.down) := by
  refine ⟨fun a => legal.1 a.down,?_⟩
  intro a b hab c hc
  exact legal.2 a.down b.down _ c hc

variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (laws : M.Calculus)
variable (seeds : M.FiniteSeedExtension) (cco : SemanticCCO.{u,v,max u v,w} S)
variable (folds : FoldCycleLaw.{u,v,w,max u v} (S := S))

include H laws seeds cco folds in
/-- CCO completion for ordinary finite chart carriers, with exactly the same
actual source calculus/seed hypotheses and only the separately proved old fold. -/
theorem finite_marked_completion_small (legal : M.LocalLegal D bits)
    (cycles : ∀ C : SimpleCycle D, CycleHom C) :
    ∃ f : DiagramHom D, ∃ mark, M.GlobalMarking mark ∧
      ∀ x, mark (f.image x) = bits x := by
  obtain ⟨f,mark,hm,hbits⟩ := finite_marked_completion M H laws seeds cco folds
    (liftDiagram D) (fun a => bits a.down) (liftDiagram_legal D M bits legal)
    (liftDiagram_cycles D cycles)
  exact ⟨lowerLiftHom D f,mark,hm,fun x => hbits (ULift.up x)⟩

end CCO.APCharacter.Completion
