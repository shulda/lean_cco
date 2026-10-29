import CCO.ProfileHelly.EdgeCompletion
import CCO.ProfileHelly.Embeddings

/-! The actual semantic CCO converse is derived AFTER the universal
algebraic fixed-vertex constructor. No semantic oracle is used in filling. -/
universe u v z
namespace CCO.ProfileHelly
variable {ι : Type u} {T : Table.{u,v} ι}

/-- Ordinary semantic completion allows collisions of nonadjacent points
and a different finite FULL allowed target. -/
def Network.Completable {V : Type z} {sort : V → ι} (D : Network T sort) : Prop :=
  ∃ (W : Type z) (_ : Finite W) (targetSort : W → ι) (N : CompleteNetwork T targetSort),
    Nonempty (D.Hom N.toNetwork)

def SemanticHomCCO (T : Table.{u,v} ι) : Prop :=
  ∀ (V : Type z) [Finite V] (sort : V → ι) (D : Network T sort),
    D.SemanticCycles ↔ D.Completable

def SemanticCCO (T : Table.{u,v} ι) : Prop :=
  ∀ (V : Type z) [Finite V] (sort : V → ι) (D : Network T sort),
    D.SemanticCycles ↔ ∃ N : CompleteNetwork T sort, D.Extends N.toNetwork

theorem profile_helly_cco (laws : TableLaws T) (helly : Word.Helly (T := T)) :
    SemanticCCO.{u,v,z} T := by
  intro V hV sort D
  constructor
  · intro cycles
    exact D.complete_of_algebraic laws helly (D.algebraic_of_semanticCycles laws cycles)
  · rintro ⟨N,hN⟩
    exact D.semanticCycles_of_hom N (Network.Hom.ofExtends D N.toNetwork hN)

/-- C22--C24: actual semantic CCO for arbitrary finite homomorphic targets.
The same-vertex constructor above proves a stronger sufficient conclusion. -/
theorem profile_helly_semantic (laws : TableLaws T) (helly : Word.Helly (T := T)) :
    SemanticHomCCO.{u,v,z} T := by
  intro V hV sort D
  constructor
  · intro cycles
    obtain ⟨N,hN⟩ := (profile_helly_cco laws helly V sort D).mp cycles
    exact ⟨V,hV,sort,N,⟨Network.Hom.ofExtends D N.toNetwork hN⟩⟩
  · rintro ⟨W,hW,targetSort,N,⟨f⟩⟩
    exact D.semanticCycles_of_hom N f

namespace Network
variable {V : Type z} [Finite V] {sort : V → ι} (D : Network T sort)

/-- A receiving consumer retains the actual completion AND literal readout
of EVERY old positive simple path between EVERY distinct endpoint pair. -/
theorem completion_with_all_path_readouts (laws : TableLaws T)
    (helly : Word.Helly (T := T)) (cycles : D.SemanticCycles) :
    ∃ N : CompleteNetwork T sort, D.Extends N.toNetwork ∧
      ∀ x y (hxy : x ≠ y) (p : D.graph.Path x y) a,
        N.edge x y = some a → a ∈ D.pathProfile hxy p := by
  obtain ⟨N,hN⟩ := (profile_helly_cco laws helly V sort D).mp cycles
  let f := Hom.ofExtends D N.toNetwork hN
  refine ⟨N,hN,?_⟩
  intro x y hxy p a ha
  exact Word.guarded_readout laws N (D.walkWord p.val (SimpleGraph.Walk.not_nil_of_ne hxy))
    (f.pointTyped x) (f.pointTyped y) (f.realizes_walk p.val _)
    hxy a ha

end Network
end CCO.ProfileHelly
