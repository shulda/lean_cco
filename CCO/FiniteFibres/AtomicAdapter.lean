import CCO.FiniteFibres.Target
import CCO.RawExact.DiagramReindex
import CCO.PairHomogeneity

/-! Actual finite original sources are explicitly enumerated as the finite
target API. Both cycle homomorphisms and whole homomorphisms are transported,
so the target CCO assumption is proved rather than a new fibre provider. -/
universe u v t
namespace CCO.FiniteFibres
open RelationalCompletion

variable {A : Type u} (S : AtomicSource.{0,u,v} Unit (fun _ => A)) [Fintype A]

def inputDiagram {n : Nat} (D : Atomic.Diagram (palette (S.Atom () ())) n) :
    PartialDiagram S (Fin n) where
  finite_type := inferInstance
  vertexSort := fun _ => ()
  edge := fun x y _ => D.edge x y
  edge_reverse := by
    intro x y _ a
    rw [D.edge_reverse x y]
    simp only [palette,Option.map_id,id_eq,S.symmetricLoop]

def inputCycle {n : Nat} (D : Atomic.Diagram (palette (S.Atom () ())) n)
    (K : CCO.SimpleCycle (inputDiagram S D)) : Atomic.SimpleCycle D where
  length := K.length
  length_ge_three := K.length_ge_three
  vertices := K.vertices
  specified := K.specified

theorem targetOfAtomic_CCO (cco : CCO.SemanticCCO.{0,u,0,v} S) :
    SemanticCCO (targetOfAtomic S) := by
  intro n D _hLocal hcycles
  have hsource : ∀ K : CCO.SimpleCycle (inputDiagram S D), CCO.CycleHom K := by
    intro K
    obtain ⟨point,_,hp⟩ := hcycles (inputCycle S D K)
    refine ⟨fun p => (Fintype.equivFin A).symm (point p),?_⟩
    intro p a ha
    exact hp p a ha
  obtain ⟨f⟩ := cco _ (inputDiagram S D) hsource
  refine ⟨{
    vertex := fun x => Fintype.equivFin A (f.point x)
    tag_eq := fun _ => Subsingleton.elim (α := Unit) _ _
    edge_eq := ?_ }⟩
  intro x y a ha
  have hne : x ≠ y := by
    rintro rfl
    rw [D.edge_self] at ha
    cases ha
  exact (targetOfAtomic_edge S _ _).trans (f.preserves_edge x y hne a ha)

variable {G : Type t} [Group G] [MulAction G A]
variable (H : HomogeneousSource S G)

/-- Every original motion induces a genuine colour-preserving permutation
of the enumerated target. The full target group is never replaced by G. -/
noncomputable def targetMotion (g : G) : Aut (targetOfAtomic S) := by
  let e := Fintype.equivFin A
  let f : Equiv.Perm (Fin (Fintype.card A)) := e.symm.trans ((MulAction.toPerm g).trans e)
  refine ⟨f,?_⟩
  intro x y
  change S.colour (i := ()) (j := ()) (e.symm (f x)) (e.symm (f y)) =
    S.colour (e.symm x) (e.symm y)
  have hx : e.symm (f x) = g • e.symm x := by
    change e.symm (e (g • e.symm x)) = _
    exact e.symm_apply_apply _
  have hy : e.symm (f y) = g • e.symm y := by
    change e.symm (e (g • e.symm y)) = _
    exact e.symm_apply_apply _
  rw [hx,hy]
  exact S.colourInvariant_of_homogeneous H g _ _

include H in theorem targetOfAtomic_transitive :
    ∀ x y : Fin (targetOfAtomic S).size,
      ∃ g : Aut (targetOfAtomic S), g • x = y := by
  intro x y
  obtain ⟨g,hg⟩ := S.original_sort_transitive_of_homogeneous H ()
    ((Fintype.equivFin A).symm x) ((Fintype.equivFin A).symm y)
  refine ⟨targetMotion S H g,?_⟩
  change Fintype.equivFin A (g • (Fintype.equivFin A).symm x) = y
  rw [hg]
  exact (Fintype.equivFin A).apply_symm_apply y

end CCO.FiniteFibres
