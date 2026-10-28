import CCO.StrongExact.TriangleFullness

/-!
# Arbitrary classes of finite complete structures over the original atom palette

Models use canonical finite vertex sets `Fin n`. No model is assumed to be
realized in the original source, and membership in a class is an arbitrary
predicate. Ordinary embeddings, heredity, AP and semantic homomorphic CCO
are explicit class properties. In particular no ambient limit, representation
bridge or source-instance hypothesis is part of the generic interfaces.
-/

universe u v w z
namespace CCO.FiniteAtomicClass
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}

structure Model (S : AtomicSource ι X) where
  size : Nat
  diagram : CompleteDiagram (S := S) (Fin size)

abbrev Model.sort (A : Model S) := A.diagram.diagram.vertexSort
def Model.colour (A : Model S) (x y : Fin A.size) : Σ i : ι, Σ j : ι, Option (S.Atom i j) :=
  ⟨A.sort x, A.sort y, if h : x = y then none else A.diagram.diagram.edge x y h⟩

structure Embedding (A B : Model S) where
  vertex : Fin A.size ↪ Fin B.size
  preserves_sort : ∀ x, B.sort (vertex x) = A.sort x
  preserves_colour : ∀ x y, B.colour (vertex x) (vertex y) = A.colour x y

/-- Only specified diversity edges must be preserved. Unconnected vertices may coincide. -/
structure Hom {V : Type z} (D : PartialDiagram S V) (B : Model S) where
  vertex : V → Fin B.size
  preserves_sort : ∀ x, B.sort (vertex x) = D.vertexSort x
  preserves_edge : ∀ (x y : V) (h : x ≠ y)
      (a : S.Atom (D.vertexSort x) (D.vertexSort y)),
    D.edge x y h = some a →
      B.colour (vertex x) (vertex y) = ⟨D.vertexSort x, D.vertexSort y, some a⟩

def Hereditary (K : Model S → Prop) : Prop :=
  ∀ {A B : Model S}, Nonempty (Embedding A B) → K B → K A

def AP (K : Model S → Prop) : Prop :=
  ∀ (C A B : Model S), K C → K A → K B →
    ∀ (eCA : Embedding C A) (eCB : Embedding C B),
      ∃ (T : Model S), K T ∧ ∃ (eAT : Embedding A T) (eBT : Embedding B T),
        ∀ x, eAT.vertex (eCA.vertex x) = eBT.vertex (eCB.vertex x)

/-- A cycle map has no conditions on chords or non-adjacent pairs. -/
def CycleHomInto {V : Type z} {D : PartialDiagram S V}
    (C : SimpleCycle D) (B : Model S) : Prop :=
  ∃ point : Fin C.length → Fin B.size,
    (∀ p, B.sort (point p) = D.vertexSort (C.vertices p)) ∧
    ∀ (p : Fin C.length)
        (a : S.Atom (D.vertexSort (C.vertices p))
          (D.vertexSort (C.vertices (cyclicNext C.length_pos p)))),
      D.edge (C.vertices p) (C.vertices (cyclicNext C.length_pos p)) (C.next_ne p) = some a →
        B.colour (point p) (point (cyclicNext C.length_pos p)) =
          ⟨D.vertexSort (C.vertices p), D.vertexSort (C.vertices (cyclicNext C.length_pos p)), some a⟩

def SemanticCCO (K : Model S → Prop) : Prop :=
  ∀ (V : Type z) (D : PartialDiagram S V),
    (∀ C : SimpleCycle D, ∃ B : Model S, K B ∧ CycleHomInto C B) →
      ∃ B : Model S, K B ∧ Nonempty (Hom D B)

namespace Model

theorem colour_self (A : Model S) (x : Fin A.size) :
    A.colour x x = ⟨A.sort x, A.sort x, none⟩ := by
  simp [colour]

theorem colour_eq_fullColour (A : Model S) (x y : Fin A.size) :
    A.colour x y = A.diagram.fullColour x y := by
  classical
  by_cases h : x = y <;>
    simp [colour, CompleteDiagram.fullColour, PartialDiagram.taggedEdge, h]

theorem colour_reverse (A : Model S) (x y : Fin A.size) :
    A.colour y x = reverseTagged S (A.colour x y) := by
  classical
  by_cases h : x = y
  · subst y
    simp [colour, reverseTagged]
  · simpa only [colour, dite_eq_right h, dite_eq_right (Ne.symm h), PartialDiagram.taggedEdge] using
      (A.diagram.diagram.taggedEdge_reverse x y h)

theorem colour_fst (A : Model S) (x y : Fin A.size) : (A.colour x y).1 = A.sort x := by
  rfl

theorem colour_snd_fst (A : Model S) (x y : Fin A.size) : (A.colour x y).2.1 = A.sort y := by
  rfl

theorem ne_of_colour_some (A : Model S) {i j : ι} {a : S.Atom i j}
    {x y : Fin A.size} (h : A.colour x y = ⟨i, j, some a⟩) : x ≠ y := by
  intro heq
  subst y
  have hh := congrArg (fun c : Σ i : ι, Σ j : ι, Option (S.Atom i j) => c.2.2.isSome) h
  simp [colour] at hh

abbrev pullback (A : Model S) {n : Nat} (e : Fin n ↪ Fin A.size) : Model S where
  size := n
  diagram := {
    diagram := {
      finite_type := inferInstance
      vertexSort x := A.sort (e x)
      edge x y h := A.diagram.diagram.edge (e x) (e y) (e.injective.ne h)
      edge_reverse x y _h a := A.diagram.diagram.edge_reverse (e x) (e y) _ a }
    complete := by
      intro x y h
      exact A.diagram.complete (e x) (e y) (e.injective.ne h) }

theorem colour_pullback (A : Model S) {n : Nat} (e : Fin n ↪ Fin A.size)
    (x y : Fin n) : (A.pullback e).colour x y = A.colour (e x) (e y) := by
  classical
  by_cases h : x = y
  · subst y
    simp [colour, pullback, sort]
  · have he : e x ≠ e y := e.injective.ne h
    simp [colour, pullback, sort, h, he]

def pullbackEmbedding (A : Model S) {n : Nat} (e : Fin n ↪ Fin A.size) : Embedding (A.pullback e) A where
  vertex := e
  preserves_sort _ := rfl
  preserves_colour x y := (A.colour_pullback e x y).symm

/-- Changing the finite enumeration transports the literal induced structure, with all colours unchanged. -/
def pullbackReindexEmbedding (A : Model S) {n m : Nat} (e : Fin m ↪ Fin A.size)
    (equiv : Fin n ≃ Fin m) : Embedding (A.pullback (equiv.toEmbedding.trans e)) (A.pullback e) where
  vertex := equiv.toEmbedding
  preserves_sort _ := rfl
  preserves_colour x y := (A.colour_pullback e (equiv x) (equiv y)).trans
    (A.colour_pullback (equiv.toEmbedding.trans e) x y).symm

def pullbackReindexInverse (A : Model S) {n m : Nat} (e : Fin m ↪ Fin A.size)
    (equiv : Fin n ≃ Fin m) : Embedding (A.pullback e) (A.pullback (equiv.toEmbedding.trans e)) where
  vertex := equiv.symm.toEmbedding
  preserves_sort x := by
    change A.sort (e (equiv (equiv.symm x))) = A.sort (e x)
    rw [equiv.apply_symm_apply]
  preserves_colour x y := by
    rw [A.colour_pullback, A.colour_pullback]
    change A.colour (e (equiv (equiv.symm x))) (e (equiv (equiv.symm y))) = A.colour (e x) (e y)
    rw [equiv.apply_symm_apply, equiv.apply_symm_apply]

end Model

/-- Every literal induced substructure of the input on at most three vertices.
Different finite enumerations preserve the entire colouring, including the diagonal. -/
def SmallSubmodels (K : Model S → Prop) (A : Model S) : Prop :=
  ∀ {n : Nat} (e : Fin n ↪ Fin A.size), n ≤ 3 → K (A.pullback e)

def Embedding.trans {A B C : Model S} (e : Embedding A B) (f : Embedding B C) : Embedding A C where
  vertex := e.vertex.trans f.vertex
  preserves_sort x := (f.preserves_sort (e.vertex x)).trans (e.preserves_sort x)
  preserves_colour x y := (f.preserves_colour (e.vertex x) (e.vertex y)).trans (e.preserves_colour x y)

/-- A complete diversity input makes its class-valued homomorphism an induced embedding. -/
def Hom.toEmbedding {A B : Model S} (f : Hom A.diagram.diagram B) : Embedding A B := by
  classical
  have hinj : Function.Injective f.vertex := by
    intro x y hxy
    by_contra hn
    obtain ⟨a, ha⟩ := A.diagram.complete x y hn
    exact B.ne_of_colour_some (f.preserves_edge x y hn a ha) hxy
  refine { vertex := ⟨f.vertex, hinj⟩, preserves_sort := f.preserves_sort, preserves_colour := ?_ }
  intro x y
  by_cases h : x = y
  · subst y
    change B.colour (f.vertex x) (f.vertex x) = A.colour x x
    rw [B.colour_self, A.colour_self, f.preserves_sort]
  · obtain ⟨a, ha⟩ := A.diagram.complete x y h
    have hc := f.preserves_edge x y h a ha
    change B.colour (f.vertex x) (f.vertex y) = A.colour x y
    have hh : A.colour x y = ⟨A.sort x, A.sort y, some a⟩ := by
      simp [Model.colour, h, ha]
    exact hc.trans hh.symm

/-- Isomorphism invariance is a consequence of hereditary closure, not an extra class premise. -/
theorem Hereditary.mem_iff_of_embeddings {K : Model S → Prop} (h : Hereditary K)
    {A B : Model S} (e : Embedding A B) (f : Embedding B A) : K A ↔ K B :=
  ⟨fun hA => h ⟨f⟩ hA, fun hB => h ⟨e⟩ hB⟩

/-- A hereditary class is independent of every choice of finite induced enumeration. -/
theorem Hereditary.pullback_reindex_iff {K : Model S → Prop} (h : Hereditary K)
    (A : Model S) {n m : Nat} (e : Fin m ↪ Fin A.size) (equiv : Fin n ≃ Fin m) :
    K (A.pullback (equiv.toEmbedding.trans e)) ↔ K (A.pullback e) :=
  h.mem_iff_of_embeddings (A.pullbackReindexEmbedding e equiv) (A.pullbackReindexInverse e equiv)

end CCO.FiniteAtomicClass
