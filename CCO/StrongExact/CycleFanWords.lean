import CCO.StrongExact.TriangleFan
import CCO.PositiveWords

/-!
# AP-only triangle fan: finite rooted chains of legal old triangles

This is the essential fan construction in the independent
AP+homomorphic-CCO triangle-fullness source proof. Every step carries
one *actual* legal triangle from the complete input's root and two
successive cycle vertices. Pair homogeneity transports that triangle
onto the already realized root-edge. No SAP, injectivity of the whole
path, strong path product, NR2 or new provider is assumed.

This module proves the full finite fan's represented path realization.
Deriving the stated triangle-fullness theorem additionally requires
extracting this fan from each simple cycle of an arbitrary complete
typed diagram, and applying CCO. That last combinatorial reduction
is a separate pending obligation.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u, v, w} ι X)
variable {i j k : ι}

/-- Rooted list of positive prescribed old edges and all intermediate
root-chord colours. Each new step is witnessed by an actual triangle;
the root/last sorts are retained dependently in the final atom. -/
inductive TriangleFan (i : ι) :
    {j : ι} → S.Atom i j → Type (max u (max v w)) where
  | first {j : ι} (a : S.Atom i j) : TriangleFan i a
  | next {j k : ι} {a : S.Atom i j}
      (fan : TriangleFan i a)
      (b : S.Atom j k) (c : S.Atom i k)
      (triangle : S.Triangle a b c) : TriangleFan i c

namespace TriangleFan

/-- Every fan is a positive diversity word from root to last vertex;
no equality can be an edge, though represented intermediate walks
may repeat nonadjacent real vertices. -/
def word {a : S.Atom i j} :
    TriangleFan S i a → PositiveWord S i j
  | .first a => .single a
  | .next fan b _ _ => PositiveWord.append S (word fan) (.single b)

/-- Realise an entire rooted fan by an actual represented positive
word whose terminal pair has precisely the last root-chord atom.
The terminal colours can be repeated named sorts and the path need not
be injective; AP triangle fullness only needs a cycle homomorphism. -/
theorem represented_fan_endpoint
    {G : Type*} [Group G] [∀ s : ι, MulAction G (X s)]
    (H : HomogeneousSource S G)
    {a : S.Atom i j} (fan : TriangleFan S i a) :
    ∃ x : X i, ∃ y : X j,
      PositiveWord.represented S (word fan) x y ∧
        S.colour x y = some a := by
  induction fan with
  | first a =>
      obtain ⟨x, y, hxy⟩ := S.realized a
      exact ⟨x, y, hxy, hxy⟩
  | @next j k a fan b c htri ih =>
      obtain ⟨x, y, hwalk, hxy⟩ := ih
      obtain ⟨z, hyz, hxz⟩ :=
        S.triangle_fan_step_of_homogeneous H a b c
          htri x y hxy
      refine ⟨x, z, ?_, hxz⟩
      rw [PositiveWord.represented_append S]
      exact ⟨y, hwalk, hyz⟩

end TriangleFan
end CCO.StrongExact
