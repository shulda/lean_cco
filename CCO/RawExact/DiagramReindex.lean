import CCO.Finite
import Mathlib.Data.Fintype.EquivFin

/-!
# Finite diagram, cycle and homomorphism reindexing

Completion on every finite ordinal is equivalent to completion on
arbitrary finite vertex types. Finite reindexing also transports the
vertex universe of semantic CCO through an actual ULift finite ordinal;
no stronger CCO premise is needed for a differently represented finite
expansion carrier.
-/

universe u v w z z' z''

namespace CCO

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

namespace PartialDiagram

/-- Pull a finite original-labelled diagram back along an embedding. -/
def reindex {V : Type z} {W : Type z'} [Finite W]
    (D : PartialDiagram S V) (e : W ↪ V) : PartialDiagram S W where
  finite_type := inferInstance
  vertexSort := fun p => D.vertexSort (e p)
  edge := fun p q hpq => D.edge (e p) (e q) (e.injective.ne hpq)
  edge_reverse := fun p q hpq a => D.edge_reverse (e p) (e q) (e.injective.ne hpq) a

end PartialDiagram

namespace SimpleCycle

/-- An actual simple cycle in a reindexed diagram is a simple cycle in
its original diagram, with the same cyclic positions and edge labels. -/
def ofReindex {V : Type z} {W : Type z'} [Finite W]
    (D : PartialDiagram S V) (e : W ↪ V)
    (C : SimpleCycle (D.reindex S e)) : SimpleCycle D where
  length := C.length
  length_ge_three := C.length_ge_three
  length_pos := C.length_pos
  vertices := C.vertices.trans e
  next_ne := fun p => e.injective.ne (C.next_ne p)
  specified := fun p => C.specified p

theorem cycleHom_ofReindex_iff {V : Type z} {W : Type z'} [Finite W]
    (D : PartialDiagram S V) (e : W ↪ V)
    (C : SimpleCycle (D.reindex S e)) :
    CycleHom (C.ofReindex S D e) ↔ CycleHom C := Iff.rfl

end SimpleCycle

namespace DiagramHom

private theorem cast_point_tag {i : ι} (p : Sigma X) (h : p.1 = i) :
    (⟨i, h ▸ p.2⟩ : Sigma X) = p := by
  cases p with
  | mk j x =>
    change j = i at h
    cases h
    rfl

/-- Actual marked image after inverse reindexing by an equivalence. -/
def reindexImage {V : Type z} {W : Type z'} [Finite W]
    (D : PartialDiagram S V) (e : W ≃ V)
    (f : DiagramHom (D.reindex S e.toEmbedding)) (p : V) : Sigma X :=
  ⟨D.vertexSort (e (e.symm p)), f.point (e.symm p)⟩

theorem reindexImage_sort {V : Type z} {W : Type z'} [Finite W]
    (D : PartialDiagram S V) (e : W ≃ V)
    (f : DiagramHom (D.reindex S e.toEmbedding)) (p : V) :
    (reindexImage S D e f p).1 = D.vertexSort p :=
  congrArg D.vertexSort (e.apply_symm_apply p)

def reindexPoint {V : Type z} {W : Type z'} [Finite W]
    (D : PartialDiagram S V) (e : W ≃ V)
    (f : DiagramHom (D.reindex S e.toEmbedding)) (p : V) : X (D.vertexSort p) :=
  reindexImage_sort S D e f p ▸ (reindexImage S D e f p).2

theorem reindexPoint_tag {V : Type z} {W : Type z'} [Finite W]
    (D : PartialDiagram S V) (e : W ≃ V)
    (f : DiagramHom (D.reindex S e.toEmbedding)) (p : V) :
    (⟨D.vertexSort p, reindexPoint S D e f p⟩ : Sigma X) = reindexImage S D e f p :=
  cast_point_tag _ (reindexImage_sort S D e f p)

theorem reindexPoint_at {V : Type z} {W : Type z'} [Finite W]
    (D : PartialDiagram S V) (e : W ≃ V)
    (f : DiagramHom (D.reindex S e.toEmbedding)) (p : W) :
    reindexPoint S D e f (e p) = f.point p := by
  have hTag :
      (⟨D.vertexSort (e p), reindexPoint S D e f (e p)⟩ : Sigma X) =
        ⟨D.vertexSort (e p), f.point p⟩ := by
    rw [reindexPoint_tag]
    exact congrArg (fun q : W => (⟨D.vertexSort (e q), f.point q⟩ : Sigma X))
      (e.symm_apply_apply p)
  exact eq_of_heq (Sigma.mk.inj hTag).2

/-- Push one reindexed diagram homomorphism to the original finite
vertex type. Every actual source atomic edge is retained. -/
def ofReindex {V : Type z} {W : Type z'} [Finite W]
    (D : PartialDiagram S V) (e : W ≃ V)
    (f : DiagramHom (D.reindex S e.toEmbedding)) : DiagramHom D where
  point := reindexPoint S D e f
  preserves_edge := by
    intro p q hpq a hEdge
    obtain ⟨p', rfl⟩ := e.surjective p
    obtain ⟨q', rfl⟩ := e.surjective q
    have hNe : p' ≠ q' := fun heq => hpq (congrArg e heq)
    have h := f.preserves_edge p' q' hNe a hEdge
    simpa only [reindexPoint_at, PartialDiagram.reindex] using h

end DiagramHom

/-- Completion on every finite ordinal gives the full accepted semantic
CCO interface over arbitrary finite vertex types, including empty ones. -/
theorem semanticCCO_of_fin
    (hFin : ∀ (n : Nat) (D : PartialDiagram S (Fin n)),
      (∀ C : SimpleCycle D, CycleHom C) → Nonempty (DiagramHom D)) :
    SemanticCCO.{u,v,z,w} S := by
  classical
  intro V D hCycles
  let : Finite V := D.finite_type
  let : Fintype V := Fintype.ofFinite V
  let e : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  let d := D.reindex S e.toEmbedding
  have hReindexed : ∀ C : SimpleCycle d, CycleHom C := by
    intro C
    exact (SimpleCycle.cycleHom_ofReindex_iff S D e.toEmbedding C).mp
      (hCycles (C.ofReindex S D e.toEmbedding))
  obtain ⟨f⟩ := hFin (Fintype.card V) d hReindexed
  exact ⟨f.ofReindex S D e⟩

/-- Semantic CCO on finite diagrams is independent of the universe used
for their formal vertices. The transport is through an actual lifted
finite ordinal, preserving every cycle and atomic colour. -/
theorem semanticCCO_change_universe
    (cco : SemanticCCO.{u,v,z,w} S) : SemanticCCO.{u,v,z',w} S := by
  classical
  intro V D hCycles
  let : Finite V := D.finite_type
  let : Fintype V := Fintype.ofFinite V
  let e : ULift.{z} (Fin (Fintype.card V)) ≃ V :=
    Equiv.ulift.trans (Fintype.equivFin V).symm
  let d := D.reindex S e.toEmbedding
  have hReindexed : ∀ C : SimpleCycle d, CycleHom C := by
    intro C
    exact (SimpleCycle.cycleHom_ofReindex_iff S D e.toEmbedding C).mp
      (hCycles (C.ofReindex S D e.toEmbedding))
  obtain ⟨f⟩ := cco _ d hReindexed
  exact ⟨f.ofReindex S D e⟩

end CCO
