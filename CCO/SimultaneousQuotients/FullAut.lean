import CCO.SimultaneousQuotients.Source
import CCO.FiniteKernel.Named.CheckSource

/-! B041 C41,C50–C54: FULL automorphisms of the actual complete named binary
quotient structure. The finite axes are entire named sorts, not finite fibres
or pointwise owner kernels. Conversion from the typed atomic language to a
unary/binary presentation preserves exactly all named predicates. -/

universe u v w t z
namespace CCO.SimultaneousQuotients
namespace FullAut

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

def binary : FiniteKernel.BinaryStructure (Sigma X) where
  Unary := ι
  Binary := Σ i, Σ j, Option (S.Atom i j)
  unary i p := p.1 = i
  binary c p q := taggedColour S p q = c

/-- The actual full binary automorphism group, preserving all original sort
names and all optional pair colours, including logical equality. -/
abbrev Aut := (binary S).Aut

variable {G : Type t} [Group G] [MulAction G (Sigma X)]
variable (H : HomogeneousSource S G)
include H

noncomputable def motion (g : G) : Aut S := by
  refine ⟨MulAction.toPerm g, ?_⟩
  constructor
  · intro i p
    change (g • p).1 = i ↔ p.1 = i
    rw [H.preserves_sort g p]
  · intro c p q
    change taggedColour S (g • p) (g • q) = c ↔ taggedColour S p q = c
    rw [H.preserves_colours g p q]

@[simp] theorem motion_apply (g : G) (p : Sigma X) :
    (motion S H g).val p = g • p := rfl

/-- No predicate or relation is forgotten when applying the general finite
entire-axis provider. Its homogeneous group is FULL Aut of this presentation;
the given original motions are only used to prove its extension property. -/
theorem homogeneous : (binary S).Homogeneous := by
  intro A f _hf _hu hb
  letI : Finite ↥A := inferInstance
  have hColour : ∀ x y : ↥A, taggedColour S x.val y.val = taggedColour S (f x) (f y) := by
    intro x y
    exact ((hb (taggedColour S x.val y.val) x y).mpr rfl).symm
  obtain ⟨g, hg⟩ := H.extends_finite_diagram (fun x : ↥A => x.val) f hColour
  exact ⟨motion S H g, hg⟩

/-- Whole named sorts, with arbitrary ambient complement. The selected index
map is injective, so the selected axes are genuinely distinct named sorts. -/
noncomputable def axes {I : Type z} (origin : I ↪ ι)
    (hFinite : ∀ i, Finite (X (origin i))) :
    FiniteKernel.NamedAxes (binary S) I where
  name := origin
  finite_axis i := by
    letI := hFinite i
    have hRange : (Set.range (fun x : X (origin i) => (⟨origin i, x⟩ : Sigma X))).Finite :=
      Set.finite_range _
    apply hRange.subset
    rintro ⟨j, x⟩ hj
    change j = origin i at hj
    subst j
    exact ⟨x, rfl⟩
  disjoint i j p hi hj := origin.injective (hi.symm.trans hj)

theorem axis_is_entire {I : Type z} (origin : I ↪ ι)
    (hFinite : ∀ i, Finite (X (origin i))) (i : I) (p : Sigma X) :
    p ∈ (axes S origin hFinite).axis i ↔ p.1 = origin i := Iff.rfl

/-- Every entire finite named quotient axis receives its FULL intrinsic group. -/
theorem projection_surjective {I : Type z} (origin : I ↪ ι)
    (hFinite : ∀ i, Finite (X (origin i))) (i : I) :
    Function.Surjective ((axes S origin hFinite).restrict i) :=
  (axes S origin hFinite).restrict_surjective (homogeneous S H) i

/-- Actual pair images are subdirect, and finite full-group images are
EXACTLY their pair constraints, including empty and singleton selections. -/
theorem finite_projection {I : Type z} (origin : I ↪ ι)
    (hFinite : ∀ i, Finite (X (origin i))) (A : Finset I)
    (p : ∀ i : ↥A, (axes S origin hFinite).Intrinsic i.val) :
    p ∈ (axes S origin hFinite).actualImage A ↔
      ∀ i j : ↥A, i.val ≠ j.val →
        (p i, p j) ∈ (axes S origin hFinite).actualPair i.val j.val :=
  (axes S origin hFinite).finite_projection (homogeneous S H) A p

theorem pair_subdirect {I : Type z} (origin : I ↪ ι)
    (hFinite : ∀ i, Finite (X (origin i))) (i j : I) :
    (∀ a : (axes S origin hFinite).Intrinsic i,
      ∃ b, (a, b) ∈ (axes S origin hFinite).actualPair i j) ∧
    (∀ b : (axes S origin hFinite).Intrinsic j,
      ∃ a, (a, b) ∈ (axes S origin hFinite).actualPair i j) :=
  ⟨(axes S origin hFinite).actual_pair_subdirect_left (homogeneous S H) i j,
   (axes S origin hFinite).actual_pair_subdirect_right (homogeneous S H) i j⟩

end FullAut
end CCO.SimultaneousQuotients
