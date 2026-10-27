import CCO.StrongExact.FinitePC
import CCO.PositiveWords

/-!
# C11: stable STRONG PC supports every specified positive path

A path is a genuinely composable sequence of *specified* old diversity
edges. Each last endpoint is different from the first endpoint of the
remaining prefix, and adjacent vertices are distinct. Every genuine
simple formal path satisfies these conditions; the theorem in fact
covers this slightly wider family of endpoint-separated walks.

This is a purely algebraic consequence of the all-third-vertex
strong PC update and B001 strong product associativity. There is no
RAW equality identity and no SAP/CCO assumption in the abstract
stable-network induction.
-/

universe u v w z

namespace CCO.StrongPC

variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u, v, w} ι X} {V : Type z}
variable (D : PartialDiagram S V)

/-- A positive sequence of literal specified old diversity edges
whose initial and final formal vertices are distinct at every
recursive stage. Genuine simple paths are instances. -/
inductive SpecifiedPath : V → V → Type (max u (max v (max w z))) where
  | edge {x y : V} (hxy : x ≠ y)
      (a : S.Atom (D.vertexSort x) (D.vertexSort y))
      (ha : D.edge x y hxy = some a) : SpecifiedPath x y
  | cons {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z)
      (a : S.Atom (D.vertexSort x) (D.vertexSort y))
      (ha : D.edge x y hxy = some a)
      (tail : SpecifiedPath y z) : SpecifiedPath x z

namespace SpecifiedPath

variable {D}

/-- The first and last formal vertices are different at every length. -/
def endpoints_ne {x y : V} : D.SpecifiedPath x y → x ≠ y
  | .edge hxy _ _ => hxy
  | .cons _ hxz _ _ _ => hxz

/-- The actual typed positive word, never an empty or identity word. -/
def word {x y : V} :
    D.SpecifiedPath x y →
      PositiveWord S (D.vertexSort x) (D.vertexSort y)
  | .edge _ a _ => .single a
  | .cons _ _ a _ tail => .cons a (word tail)

/-- C11: a stable refinement of the initial singleton/Top network
is contained in the STRONG profile of each specified endpoint-separated
positive path. No extra product exactness or CCO hypothesis is used. -/
theorem stable_subset_profile
    (N : Network D) (hStable : Stable D N)
    (hInit : Refines D N (initial D))
    {x y : V} (p : D.SpecifiedPath x y) :
    N ⟨x, y, p.endpoints_ne⟩ ⊆ PositiveWord.profile S p.word := by
  induction p with
  | edge hxy a ha =>
      intro c hc
      have h := hInit ⟨_, _, hxy⟩ hc
      change c ∈ D.initial ⟨_, _, hxy⟩ at h
      simp only [initial, ha, Set.mem_singleton_iff] at h
      change c ∈ ({a} : S.Menu _ _)
      exact h
  | @cons x y z hxy hxz a ha tail ih =>
      intro c hc
      have hcStep : c ∈ step D N ⟨x, z, hxz⟩ := by
        rw [hStable ⟨x, z, hxz⟩]
        exact hc
      have hcProduct : c ∈ S.product
          (N ⟨x, y, hxy⟩)
          (N ⟨y, z, tail.endpoints_ne⟩) :=
        hcStep.2 y hxy tail.endpoints_ne
      have hFirst : N ⟨x, y, hxy⟩ ⊆ ({a} : S.Menu _ _) := by
        intro b hb
        have h := hInit ⟨x, y, hxy⟩ hb
        simpa only [initial, ha, Set.mem_singleton_iff] using h
      change c ∈ S.product ({a} : S.Menu _ _)
        (PositiveWord.profile S tail.word)
      exact S.product_mono hFirst ih hcProduct

end SpecifiedPath

/-- Every iterate refines its starting network. -/
theorem iterate_refines_start (N : Network D) (n : Nat) :
    Refines D (iterate D N n) N := by
  induction n with
  | zero =>
      intro p a ha
      exact ha
  | succ n ih =>
      intro p a ha
      exact ih p ((iterate_succ_refines D N n) p ha)

/-- The stationary PC network still respects all displayed singleton
constraints on original specified edges. -/
theorem fixedNetwork_refines_initial :
    Refines D (fixedNetwork D) (initial D) :=
  iterate_refines_start D (initial D) (fixedIndex D)

/-- C11 finite fixed-point corollary: every fixed survivor atom belongs
to every specified path profile, with all intermediate sorts retained. -/
theorem fixedNetwork_subset_path_profile {x y : V}
    (p : D.SpecifiedPath x y) :
    (fixedNetwork D) ⟨x, y, p.endpoints_ne⟩ ⊆
      PositiveWord.profile S p.word :=
  p.stable_subset_profile (fixedNetwork D)
    (fixedNetwork_stable D) (fixedNetwork_refines_initial D)

end CCO.StrongPC
