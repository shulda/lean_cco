import CCO.Atomic

/-!
# Finite real diagrams, embeddings, cycles, and semantic interfaces

`FiniteInduced` is a genuinely complete induced **real** substructure:
the entire colour on every pair is inherited from the actual source.
`PartialDiagram` separately represents a finite list of diversity
constraints.  Missing edges do not assert inequality and may be collapsed
by a `DiagramHom`.  The CCO interface counts simple cycles of length at
least three only, never parallel edges or invented diagonal edges.
-/

universe u v w z t

namespace CCO

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource ι X)

/-- Sort-pair tags are retained in the type of the colour. -/
def taggedColour (p q : Sigma X) :
    (Σ i : ι, Σ j : ι, Option (S.Atom i j)) :=
  ⟨p.1, q.1, S.colour p.2 q.2⟩

structure FiniteInduced where
  vertices : Set (Sigma X)
  finite_vertices : vertices.Finite

/-- A finite induced embedding preserves all old literal atoms, including
the real diagonal, not merely the currently specified diversity edges. -/
structure InducedEmbedding (A B : FiniteInduced (X := X)) where
  toEmbedding : (↥A.vertices) ↪ (↥B.vertices)
  preserves_sort : ∀ p, ((toEmbedding p).val).1 = (p.val).1
  preserves_colours : ∀ p q,
    taggedColour S p.val q.val =
      taggedColour S (toEmbedding p).val (toEmbedding q).val

/-- Finite partial labelled simple diagrams. Only distinct formal vertices
can have edges, and `none` signifies a missing constraint. -/
structure PartialDiagram (V : Type z) where
  finite_type : Finite V
  vertexSort : V → ι
  edge : ∀ (x y : V), x ≠ y →
    Option (S.Atom (vertexSort x) (vertexSort y))
  edge_reverse : ∀ (x y : V) (h : x ≠ y)
      (a : S.Atom (vertexSort x) (vertexSort y)),
    edge x y h = some a ↔ edge y x h.symm = some (S.conv a)

variable {S} {V : Type z}

/-- Homomorphism into the actual source: no injectivity assumption.
Only recorded edges need be preserved, and these are irreflexive. -/
structure DiagramHom (D : PartialDiagram S V) where
  point : ∀ x : V, X (D.vertexSort x)
  preserves_edge : ∀ (x y : V) (h : x ≠ y)
      (a : S.Atom (D.vertexSort x) (D.vertexSort y)),
    D.edge x y h = some a → S.colour (point x) (point y) = some a

def DiagramHom.image {D : PartialDiagram S V} (f : DiagramHom D)
    (x : V) : Sigma X :=
  ⟨D.vertexSort x, f.point x⟩

/-- An injective realization, unlike an unrestricted homomorphism, separates
all formal vertices, including vertices with the same named sort. -/
def DiagramHom.IsInjective {D : PartialDiagram S V}
    (f : DiagramHom D) : Prop :=
  Function.Injective f.image

def PartialDiagram.IsComplete (D : PartialDiagram S V) : Prop :=
  ∀ (x y : V) (h : x ≠ y),
    ∃ a : S.Atom (D.vertexSort x) (D.vertexSort y),
      D.edge x y h = some a

structure CompleteDiagram (V : Type z) where
  diagram : PartialDiagram S V
  complete : diagram.IsComplete

/-- Cyclic successor of a nonempty finite ordinal. -/
def cyclicNext {n : Nat} (hn : 0 < n) (p : Fin n) : Fin n :=
  ⟨(p.val + 1) % n, Nat.mod_lt _ hn⟩

/-- A genuine simple cycle: no repeated formal vertices, at least three
vertices, and every edge of the cycle is a specified diversity edge.
The redundant adjacent-distinctness field exposes the proof required by
the partial-diagram edge API. -/
structure SimpleCycle (D : PartialDiagram S V) where
  length : Nat
  length_ge_three : 3 ≤ length
  length_pos : 0 < length
  vertices : Fin length ↪ V
  next_ne : ∀ p, vertices p ≠ vertices (cyclicNext length_pos p)
  specified : ∀ p,
    ∃ a : S.Atom (D.vertexSort (vertices p))
        (D.vertexSort (vertices (cyclicNext length_pos p))),
      D.edge (vertices p) (vertices (cyclicNext length_pos p))
        (next_ne p) = some a

/-- A cycle homomorphism may collide non-adjacent vertices. -/
def CycleHom {D : PartialDiagram S V} (C : SimpleCycle D) : Prop :=
  ∃ point : ∀ p : Fin C.length, X (D.vertexSort (C.vertices p)),
    ∀ (p : Fin C.length)
        (a : S.Atom (D.vertexSort (C.vertices p))
          (D.vertexSort (C.vertices (cyclicNext C.length_pos p)))),
      D.edge (C.vertices p) (C.vertices (cyclicNext C.length_pos p))
          (C.next_ne p) = some a →
        S.colour (point p) (point (cyclicNext C.length_pos p)) = some a

/-- Homomorphic simple-cycle completion (CCO). This is *only* an
interface here. There is no CCO completion theorem in B001. -/
def SemanticCCO (S : AtomicSource ι X) : Prop :=
  ∀ (V : Type z) (D : PartialDiagram S V),
    (∀ C : SimpleCycle D, CycleHom C) →
      _root_.Nonempty (DiagramHom D)

/-- A precise semantic interface for strong amalgamation of the *actual*
finite induced age. The two copies agree over the designated base and
have no additional common points. SAP here is a hypothesis and cannot be
inferred from homomorphic CCO or ordinary AP. -/
structure AgeSAP (S : AtomicSource ι X) : Prop where
  strong_amalgamate : ∀ (C A B : FiniteInduced (X := X))
      (eCA : InducedEmbedding S C A) (eCB : InducedEmbedding S C B),
    ∃ (D : FiniteInduced (X := X))
      (eAD : InducedEmbedding S A D)
      (eBD : InducedEmbedding S B D),
      (∀ c : ↥C.vertices,
        eAD.toEmbedding (eCA.toEmbedding c) =
          eBD.toEmbedding (eCB.toEmbedding c)) ∧
      (∀ a : ↥A.vertices, ∀ b : ↥B.vertices,
        eAD.toEmbedding a = eBD.toEmbedding b →
          ∃ c : ↥C.vertices,
            eCA.toEmbedding c = a ∧ eCB.toEmbedding c = b)

/-- The actual finite-partial-isomorphism extension property for an
ambient group of sort- and colour-preserving automorphisms. This is a
source hypothesis, not an unproved axiom or a conclusion of CCO. -/
structure HomogeneousSource (S : AtomicSource ι X) (G : Type t) [Group G]
    [MulAction G (Sigma X)] : Prop where
  preserves_sort : ∀ (g : G) (p : Sigma X), (g • p).1 = p.1
  preserves_colours : ∀ (g : G) (p q : Sigma X),
    taggedColour S (g • p) (g • q) = taggedColour S p q
  /-- All finite complete typed tuples, including repeated real values,
  extend when every ordered pair retains its full atomic colour. This
  is the usual induced-partial-isomorphism homogeneity phrased without
  arbitrary enumerations of finite substructures. Real equality is
  encoded by the optional diagonal and hence collisions are respected. -/
  extends_finite_diagram : ∀ {V : Type z} [Finite V]
      (f h : V → Sigma X),
    (∀ v w, taggedColour S (f v) (f w) =
      taggedColour S (h v) (h w)) →
    ∃ g : G, ∀ v, g • f v = h v

/-- The tuple form of finite homogeneity supplies the traditional finite
induced-embedding extension theorem; surjectivity onto a displayed
codomain is not needed, since its finite image is itself induced. -/
theorem HomogeneousSource.extends_partial_iso
    {G : Type t} [Group G] [MulAction G (Sigma X)]
    (H : HomogeneousSource S G)
    (A B : FiniteInduced (X := X))
    (e : InducedEmbedding S A B) :
    ∃ g : G, ∀ p : ↥A.vertices,
      g • p.val = (e.toEmbedding p).val := by
  letI : Finite ↥A.vertices := A.finite_vertices.to_subtype
  let f : ↥A.vertices → Sigma X := fun p => p.val
  let h : ↥A.vertices → Sigma X := fun p => (e.toEmbedding p).val
  have hcol : ∀ p q, taggedColour S (f p) (f q) =
      taggedColour S (h p) (h q) := by
    intro p q
    exact e.preserves_colours p q
  exact H.extends_finite_diagram f h hcol

end CCO
