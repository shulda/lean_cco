import CCO.Injectivization
import CCO.FiniteHelpers

/-! An exact specified-cycle walk is made SIMPLE over one complete old
base. Only the original consecutive cycle constraints are retained; the
whole original finite base stays literal, and every unpinned position is
fresh from it. No CCO is used and no cycle label is replaced. -/

universe u v w z t
namespace CCO.OldIdempotentForest

variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {V : Type z} {D : PartialDiagram S V}

def cyclePair (C : SimpleCycle D) (p q : Fin C.length) : Prop :=
  q = cyclicNext C.length_pos p ∨ p = cyclicNext C.length_pos q

theorem cyclePair_symm (C : SimpleCycle D) (p q : Fin C.length) :
    cyclePair C p q ↔ cyclePair C q p := or_comm

/-- The ordinary partial diagram of JUST this specified cycle, with its
original sorts and fine atoms. Unknown chords impose no extra condition. -/
noncomputable def specifiedCycleDiagram (C : SimpleCycle D) : PartialDiagram S (Fin C.length) := by
  classical
  exact {
    finite_type := inferInstance
    vertexSort := fun p => D.vertexSort (C.vertices p)
    edge := fun p q hpq => if cyclePair C p q then
      D.edge (C.vertices p) (C.vertices q) (fun he => hpq (C.vertices.injective he)) else none
    edge_reverse := by
      intro p q hpq a
      by_cases h : cyclePair C p q
      · have h' := (cyclePair_symm C p q).mp h
        simp only [ite_eq_left h,ite_eq_left h']
        exact D.edge_reverse _ _ _ a
      · have h' : ¬ cyclePair C q p := fun hr => h ((cyclePair_symm C q p).mp hr)
        simp only [ite_eq_right h,ite_eq_right h',reduceCtorEq] }

theorem specifiedCycleDiagram_next (C : SimpleCycle D) (p : Fin C.length) :
    ∀ a, (specifiedCycleDiagram C).edge p (cyclicNext C.length_pos p)
      (fun he => C.next_ne p (congrArg C.vertices he)) = some a ↔
      D.edge (C.vertices p) (C.vertices (cyclicNext C.length_pos p)) (C.next_ne p) = some a := by
  classical
  intro a
  change S.Atom (D.vertexSort (C.vertices p))
    (D.vertexSort (C.vertices (cyclicNext C.length_pos p))) at a
  change (if cyclePair C p (cyclicNext C.length_pos p) then _ else none) = some a ↔ _
  have hp : cyclePair C p (cyclicNext C.length_pos p) := Or.inl rfl
  rw [ite_eq_left hp]
  rfl

/-- A walk of the actual specified cycle is an actual diagram homomorphism
of its finite consecutive-edge diagram, including the closing edge. -/
noncomputable def cycleDiagramHom (C : SimpleCycle D)
    (point : ∀ p : Fin C.length, X (D.vertexSort (C.vertices p)))
    (edges : ∀ (p : Fin C.length)
      (a : S.Atom (D.vertexSort (C.vertices p))
        (D.vertexSort (C.vertices (cyclicNext C.length_pos p)))),
      D.edge (C.vertices p) (C.vertices (cyclicNext C.length_pos p)) (C.next_ne p) = some a →
        S.colour (point p) (point (cyclicNext C.length_pos p)) = some a) :
    DiagramHom (specifiedCycleDiagram C) where
  point := point
  preserves_edge := by
    classical
    intro p q hpq a ha
    change (if cyclePair C p q then D.edge (C.vertices p) (C.vertices q) _ else none) = some a at ha
    by_cases h : cyclePair C p q
    · rw [ite_eq_left h] at ha
      rcases h with rfl | rfl
      · exact edges p a ha
      · have hrev := (D.edge_reverse _ _ _ a).mp ha
        have hc := edges q (S.conv a) hrev
        exact (S.colour_swap _ _ a).mpr hc
    · simp only [ite_eq_right h,reduceCtorEq] at ha

structure ExactSimpleCycle (C : SimpleCycle D) where
  point : ∀ p : Fin C.length, X (D.vertexSort (C.vertices p))
  injective : Function.Injective (fun p => (⟨D.vertexSort (C.vertices p),point p⟩ : Sigma X))
  edges : ∀ (p : Fin C.length)
    (a : S.Atom (D.vertexSort (C.vertices p))
      (D.vertexSort (C.vertices (cyclicNext C.length_pos p)))),
    D.edge (C.vertices p) (C.vertices (cyclicNext C.length_pos p)) (C.next_ne p) = some a →
      S.colour (point p) (point (cyclicNext C.length_pos p)) = some a

def ExactSimpleCycle.image (C : SimpleCycle D) (R : ExactSimpleCycle C) (p : Fin C.length) : Sigma X :=
  ⟨D.vertexSort (C.vertices p),R.point p⟩

structure CompleteCycleReconstruction (C : SimpleCycle D) (A : FiniteInduced (X := X))
    (pins : Set (Fin C.length))
    (original : ∀ p : Fin C.length, X (D.vertexSort (C.vertices p))) where
  base : FiniteInduced (X := X)
  old_subset : A.vertices ⊆ base.vertices
  cycle : ExactSimpleCycle C
  inside : ∀ p, cycle.image C p ∈ base.vertices
  fixed : ∀ p ∈ pins, cycle.point p = original p
  fresh : ∀ p ∉ pins, cycle.image C p ∉ A.vertices

/-- After the original interval/anchor words have supplied their exact
cycle walk, actual SAP produces a simple realization in ONE finite
complete extension while fixing every retained old representative. -/
theorem exact_simple_cycle_over_complete_base
    {G : Type t} [Group G] [∀ i, MulAction G (X i)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (C : SimpleCycle D) (A : FiniteInduced (X := X))
    (point : ∀ p : Fin C.length, X (D.vertexSort (C.vertices p)))
    (edges : ∀ (p : Fin C.length)
      (a : S.Atom (D.vertexSort (C.vertices p))
        (D.vertexSort (C.vertices (cyclicNext C.length_pos p)))),
      D.edge (C.vertices p) (C.vertices (cyclicNext C.length_pos p)) (C.next_ne p) = some a →
        S.colour (point p) (point (cyclicNext C.length_pos p)) = some a)
    (pins : Set (Fin C.length))
    (hPin : ∀ p ∈ pins, ∀ q ∈ pins,
      (⟨D.vertexSort (C.vertices p),point p⟩ : Sigma X) =
        ⟨D.vertexSort (C.vertices q),point q⟩ → p = q) :
    Nonempty (CompleteCycleReconstruction C A pins point) := by
  classical
  let f₀ := cycleDiagramHom C point edges
  obtain ⟨f,hf,hfixed,hfresh⟩ := DiagramHom.injectivize_of_SAP H sap f₀ pins hPin
    A.vertices A.finite_vertices
  let R : ExactSimpleCycle C := {
    point := f.point
    injective := hf
    edges := fun p a ha => f.preserves_edge _ _
      (fun he => C.next_ne p (congrArg C.vertices he)) a ((specifiedCycleDiagram_next C p a).mpr ha) }
  refine ⟨{
    base := ⟨A.vertices ∪ Set.range f.image,A.finite_vertices.union (Set.finite_range _)⟩
    old_subset := fun _ h => Or.inl h
    cycle := R
    inside := fun p => Or.inr ⟨p,rfl⟩
    fixed := ?_
    fresh := hfresh }⟩
  intro p hp
  have he := hfixed p hp
  change f.point p = f₀.point p
  simpa only [DiagramHom.image,Sigma.mk.injEq,heq_eq_eq,true_and] using he

def CompleteCycleReconstruction.old_embedding (C : SimpleCycle D) (A : FiniteInduced (X := X))
    (pins : Set (Fin C.length)) (original : ∀ p : Fin C.length, X (D.vertexSort (C.vertices p)))
    (out : CompleteCycleReconstruction C A pins original) : InducedEmbedding S A out.base :=
  inducedInclusion S A out.base out.old_subset

end CCO.OldIdempotentForest
