import CCO.UnaryFreshFrames.Language
import Mathlib.Data.Set.Finite.Range

/-! The entire hereditary age: EVERY finite unary-closed induced subset.
These objects can contain hidden vertices without internal real generators.
The isomorphic-image formulation of the age is equivalent to these actual
subsets; no point-generated restriction is made. -/
universe u v
namespace CCO.UnaryFreshFrames.Structure
variable {L : Language.{u}} {V : Type v} (H : Structure L V)

structure Piece where
  points : Set V
  finite : points.Finite
  closed : H.Closed points

namespace Piece
variable {H}

instance (A : H.Piece) : Finite A.points := A.finite.to_subtype

def empty : H.Piece := ⟨∅, Set.finite_empty, H.closed_empty⟩

def union (A B : H.Piece) : H.Piece :=
  ⟨A.points ∪ B.points, A.finite.union B.finite, H.closed_union A.closed B.closed⟩

def func (A : H.Piece) (F : L.Func) (x : A.points) : A.points :=
  ⟨H.func F x.val, A.closed F x.val x.property⟩

/-- An induced embedding of A into an arbitrary subset B of the SAME H.
The target need not itself be a Piece for this definition. -/
structure Embedding (A : H.Piece) (B : Set V) where
  point : A.points → V
  mem_point : ∀ x, point x ∈ B
  injective : Function.Injective point
  sort_eq : ∀ x, H.sort (point x) = H.sort x.val
  func_eq : ∀ F x, point (A.func F x) = H.func F (point x)
  rel_iff : ∀ R (xs : Fin (L.arity R) → A.points),
    H.rel R (point ∘ xs) ↔ H.rel R (Subtype.val ∘ xs)

namespace Embedding
variable {A B C : H.Piece} {T T' : Set V}

def inclusion (h : A.points ⊆ T) : A.Embedding T where
  point := Subtype.val
  mem_point x := h x.property
  injective := Subtype.val_injective
  sort_eq _ := rfl
  func_eq _ _ := rfl
  rel_iff _ _ := Iff.rfl

def identity (A : H.Piece) : A.Embedding A.points := inclusion (Set.Subset.refl _)

def ambient (f : A.Embedding T) : A.Embedding Set.univ :=
  { f with mem_point := fun _ => Set.mem_univ _ }

def restrictTarget (f : A.Embedding T) (h : ∀ x, f.point x ∈ T') :
    A.Embedding T' := { f with mem_point := h }

def comp (g : B.Embedding T) (f : A.Embedding B.points) : A.Embedding T where
  point x := g.point ⟨f.point x, f.mem_point x⟩
  mem_point _ := g.mem_point _
  injective := by
    intro x y h
    exact f.injective (congrArg Subtype.val (g.injective h))
  sort_eq x := (g.sort_eq _).trans (f.sort_eq x)
  func_eq F x := by
    have he : (⟨f.point (A.func F x), f.mem_point _⟩ : B.points) =
        B.func F ⟨f.point x, f.mem_point x⟩ := Subtype.ext (f.func_eq F x)
    exact (congrArg g.point he).trans (g.func_eq _ _)
  rel_iff R xs := (g.rel_iff R (fun i => ⟨f.point (xs i), f.mem_point _⟩)).trans
    (f.rel_iff R xs)

def image (f : A.Embedding T) : H.Piece where
  points := Set.range f.point
  finite := Set.finite_range _
  closed := by
    rintro F _ ⟨x, rfl⟩
    exact ⟨A.func F x, f.func_eq F x⟩

def toImage (f : A.Embedding T) : A.Embedding f.image.points :=
  { f with mem_point := fun x => ⟨x, rfl⟩ }

/-- Apply an actual FULL named automorphism to the entire old map. -/
def mapAut (g : H.Aut) (f : A.Embedding T) :
    A.Embedding ((fun x => g • x) '' T) where
  point x := g • f.point x
  mem_point x := ⟨f.point x, f.mem_point x, rfl⟩
  injective := by
    intro x y h
    apply f.injective
    exact MulAction.injective g h
  sort_eq x := (H.aut_sort g _).trans (f.sort_eq x)
  func_eq F x := (congrArg (fun z => g • z) (f.func_eq F x)).trans (H.aut_func g F _)
  rel_iff R xs := (H.aut_rel g R (f.point ∘ xs)).trans (f.rel_iff R xs)

end Embedding

/-- A full automorphism carries a closed finite piece to an actual closed one. -/
def mapAut (g : H.Aut) (A : H.Piece) : H.Piece :=
  ((Embedding.identity A).mapAut g).image

end Piece

/-- Standard homogeneity, written as alignment of TWO actual induced copies
of the same finite closed object. This includes arbitrary orphan hidden bases. -/
def Homogeneous : Prop :=
  ∀ (A : H.Piece) (f g : A.Embedding Set.univ),
    ∃ a : H.Aut, ∀ x, a • f.point x = g.point x

/-- Strong amalgamation of ALL finite closed induced pieces of H. Arbitrary
isomorphic presentations are represented by the actual embeddings; D is
itself an induced age object, with no free-cross-relation requirement. -/
def AgeSAP : Prop :=
  ∀ (A B C : H.Piece) (s : A.Embedding B.points) (t : A.Embedding C.points),
    ∃ (D : H.Piece) (l : B.Embedding D.points) (r : C.Embedding D.points),
      (∀ x, l.point ⟨s.point x, s.mem_point x⟩ = r.point ⟨t.point x, t.mem_point x⟩) ∧
      ∀ x y, l.point x = r.point y → ∃ a, s.point a = x.val ∧ t.point a = y.val

end CCO.UnaryFreshFrames.Structure
