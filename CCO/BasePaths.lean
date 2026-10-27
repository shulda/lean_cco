import CCO.Atomic

/-!
# Independent consumer: finite base-path STRONG menus

This module deliberately imports only the public atomic/strong Boolean core.
The carrier of a base is a finite type of *actual* real vertices, with
literal incident source colours; the base may be empty.  A map on base
indices must cover the WHOLE designated target base, not merely have its
image as a subset.
-/

universe u v w z t

namespace CCO.AtomicSource

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource ι X) {i j : ι}

/-- Two consecutive *actual* diversity atoms through a typed intermediate
root. The intermediate sort is retained inside the dependent pair. -/
abbrev TwoStep (i j : ι) :=
  Σ k : ι, S.Atom i k × S.Atom k j

def via (d : S.TwoStep i j) : S.Menu i j :=
  S.product ({d.2.1} : S.Menu i d.1) ({d.2.2} : S.Menu d.1 j)

/-- Intersection of the source's literal two-edge STRONG menus. -/
def domain {C : Type z} (e : C → S.TwoStep i j) : S.Menu i j :=
  { c | ∀ p : C, c ∈ S.via (e p) }

/-- No base vertices imposes no restrictions: the empty meet is STRONG Top,
not RAW identity (even when the endpoint sorts coincide). -/
theorem domain_empty :
    S.domain (C := Empty) (fun c => nomatch c) = (Set.univ : S.Menu i j) := by
  ext a
  constructor
  · intro _
    trivial
  · intro _ c
    exact c.elim

/-- Onto reindexing is exactly what preserves the whole designated base. -/
theorem domain_reindex {C : Type z} {D : Type t}
    (f : C → D) (hf : Function.Surjective f)
    (e : D → S.TwoStep i j) :
    S.domain (e ∘ f) = S.domain e := by
  ext a
  constructor
  · intro h d
    obtain ⟨c, rfl⟩ := hf d
    exact h c
  · intro h c
    exact h (f c)

/-- Source-colour-preserving onto-base maps preserve the exact Boolean
base-path subset, with neither a selector nor a CCO assumption. -/
theorem domain_natural {C : Type z} {D : Type t}
    (f : C → D) (hf : Function.Surjective f)
    (e : C → S.TwoStep i j) (e' : D → S.TwoStep i j)
    (hcol : ∀ c, e c = e' (f c)) :
    S.domain e = S.domain e' := by
  have he : e = e' ∘ f := by
    funext c
    exact hcol c
  rw [he]
  exact S.domain_reindex f hf e'

def flip (d : S.TwoStep i j) : S.TwoStep j i :=
  ⟨d.1, (S.conv d.2.2, S.conv d.2.1)⟩

theorem opposite_singleton {k l : ι} (a : S.Atom k l) :
    S.opposite ({a} : S.Menu k l) =
      ({S.conv a} : S.Menu l k) := by
  ext b
  change S.conv b = a ↔ b = S.conv a
  constructor
  · intro hb
    have hh := congrArg (fun x => S.conv x) hb
    simpa only [S.conv_invol] using hh
  · intro hb
    subst b
    exact S.conv_invol a

theorem opposite_via (d : S.TwoStep i j) :
    S.opposite (S.via d) = S.via (S.flip d) := by
  rcases d with ⟨k, ⟨a, b⟩⟩
  change S.opposite (S.product ({a} : S.Menu i k) ({b} : S.Menu k j)) =
    S.product ({S.conv b} : S.Menu j k) ({S.conv a} : S.Menu k i)
  rw [S.product_opposite, S.opposite_singleton, S.opposite_singleton]

theorem opposite_domain {C : Type z}
    (e : C → S.TwoStep i j) :
    S.opposite (S.domain e) =
      S.domain (fun c => S.flip (e c)) := by
  ext a
  constructor
  · intro h c
    have hc : S.conv a ∈ S.via (e c) := h c
    have hop : a ∈ S.opposite (S.via (e c)) := hc
    rwa [S.opposite_via] at hop
  · intro h c
    have hc : a ∈ S.via (S.flip (e c)) := h c
    have hop : a ∈ S.opposite (S.via (e c)) := by
      rw [S.opposite_via]
      exact hc
    exact hop

/-- A finite actual span: a left root, a right root and a finite set
of distinct designated base points, together with their *literal* atoms.
The incident-colour proofs guarantee no base/root collisions even if
the sort labels repeat. -/
structure ActualSpan (C : Type z) where
  finiteBase : Finite C
  baseSort : C → ι
  point : ∀ c : C, X (baseSort c)
  left : X i
  right : X j
  leftAtom : ∀ c, S.Atom i (baseSort c)
  rightAtom : ∀ c, S.Atom (baseSort c) j
  leftColour : ∀ c, S.colour left (point c) = some (leftAtom c)
  rightColour : ∀ c, S.colour (point c) right = some (rightAtom c)
  baseInjective :
    Function.Injective (fun c => (⟨baseSort c, point c⟩ : Sigma X))
  distinctRoots : (⟨i, left⟩ : Sigma X) ≠ ⟨j, right⟩

namespace ActualSpan

variable {C : Type z}
variable {S} (A : S.ActualSpan (i := i) (j := j) C)

def edges (c : C) : S.TwoStep i j :=
  ⟨A.baseSort c, (A.leftAtom c, A.rightAtom c)⟩

def menu : S.Menu i j :=
  S.domain A.edges

/-- The actual tagged vertices of the designated common base. Distinct
formal base indices denote different real vertices by baseInjective. -/
def baseVertices : Set (Sigma X) :=
  Set.range (fun c : C => (⟨A.baseSort c, A.point c⟩ : Sigma X))

/-- Minimal actual left factor of the finite span. -/
def leftFactorVertices : Set (Sigma X) :=
  Set.insert (⟨i, A.left⟩ : Sigma X) A.baseVertices

/-- Minimal actual right factor of the finite span. -/
def rightFactorVertices : Set (Sigma X) :=
  Set.insert (⟨j, A.right⟩ : Sigma X) A.baseVertices

theorem baseVertices_finite : A.baseVertices.Finite := by
  letI : Finite C := A.finiteBase
  exact Set.finite_range _

/-- The finite displayed base does not accidentally include the left
endpoint, even when its named sort matches a base sort. -/
theorem leftRoot_not_base :
    (⟨i, A.left⟩ : Sigma X) ∉ A.baseVertices := by
  rintro ⟨c, hc⟩
  exact (S.atomRel_ne (A.leftColour c)) hc.symm

theorem rightRoot_not_base :
    (⟨j, A.right⟩ : Sigma X) ∉ A.baseVertices := by
  rintro ⟨c, hc⟩
  exact (S.atomRel_ne (A.rightColour c)) hc

/-- The two minimal ACTUAL factors intersect exactly in the displayed
base, not merely in a subset of it. This is true independently of
whether the two endpoint sort labels coincide. -/
theorem factor_intersection :
    A.leftFactorVertices ∩ A.rightFactorVertices = A.baseVertices := by
  ext p
  constructor
  · rintro ⟨hl, hr⟩
    rcases (Set.mem_insert_iff.mp hl) with hleft | hbase
    · rcases (Set.mem_insert_iff.mp hr) with hright | hbase
      · exact False.elim (A.distinctRoots (hleft.symm.trans hright))
      · exact hbase
    · exact hbase
  · intro hb
    change p ∈ Set.insert (⟨i, A.left⟩ : Sigma X) A.baseVertices ∧
      p ∈ Set.insert (⟨j, A.right⟩ : Sigma X) A.baseVertices
    exact ⟨Set.mem_insert_iff.mpr (Or.inr hb),
      Set.mem_insert_iff.mpr (Or.inr hb)⟩

theorem empty_base (A : S.ActualSpan (i := i) (j := j) Empty) :
    A.menu = Set.univ := by
  ext a
  constructor
  · intro _
    trivial
  · intro _ c
    exact c.elim

/-- Flip the actual finite span, including the literal converse edges. -/
def reverse : S.ActualSpan (i := j) (j := i) C where
  finiteBase := A.finiteBase
  baseSort := A.baseSort
  point := A.point
  left := A.right
  right := A.left
  leftAtom := fun c => S.conv (A.rightAtom c)
  rightAtom := fun c => S.conv (A.leftAtom c)
  leftColour := by
    intro c
    exact (S.colour_swap (A.point c) A.right (A.rightAtom c)).mp (A.rightColour c)
  rightColour := by
    intro c
    exact (S.colour_swap A.left (A.point c) (A.leftAtom c)).mp (A.leftColour c)
  baseInjective := A.baseInjective
  distinctRoots := by
    intro heq
    exact A.distinctRoots heq.symm

theorem menu_reverse :
    S.opposite A.menu = A.reverse.menu := by
  exact S.opposite_domain A.edges

end ActualSpan

/-- An onto designated-base map preserving literal pair colour names.
This is the precise hypothesis induced by factor embeddings of the
whole span; vertices may be added outside the designated target base. -/
structure OntoBaseMap {C : Type z} {D : Type t}
    (A : S.ActualSpan (i := i) (j := j) C)
    (B : S.ActualSpan (i := i) (j := j) D) where
  baseMap : C → D
  baseOnto : Function.Surjective baseMap
  preservesOldEdges :
    ∀ c, A.edges c = B.edges (baseMap c)

theorem menu_preserved {C : Type z} {D : Type t}
    (A : S.ActualSpan (i := i) (j := j) C)
    (B : S.ActualSpan (i := i) (j := j) D)
    (f : S.OntoBaseMap A B) :
    A.menu = B.menu :=
  S.domain_natural f.baseMap f.baseOnto A.edges B.edges f.preservesOldEdges

end CCO.AtomicSource
