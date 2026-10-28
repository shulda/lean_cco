import CCO.Stabilizer
import CCO.Finite
import Mathlib.Data.Fintype.Option

/-!
# Pointwise stabilizer orbits from finite complete homogeneity

No orbit-infinitude premise is made here. Two real points realizing the
same complete finite-colour type over an actual finite real base lie in
one orbit of the pointwise stabilizer. This is an elementary consequence
of the source's finite homogeneous tuple extension property and will be
used together with *derived* age-SAP multiplicity.
-/

universe u v w

namespace CCO.RealAction

variable {ι : Type u} {X : ι → Type v}
variable {G : Type*} [Group G] [MulAction G (Sigma X)]
variable (S : AtomicSource ι X)

/-- An explicit finite complete one-point type over B, including BOTH
orientations and the actual logical diagonal. This formulation works
also when the proposed new point lies inside the displayed base. -/
def SameTypeOver (B : FiniteInduced (X := X))
    (x y : Sigma X) : Prop :=
  taggedColour S x x = taggedColour S y y ∧
  (∀ b ∈ B.vertices, taggedColour S x b = taggedColour S y b) ∧
  (∀ b ∈ B.vertices, taggedColour S b x = taggedColour S b y)

/-- Homogeneity realizes equality of complete finite types by one
automorphism fixing the base pointwise. The base is a SET of actual
values, not an injectively indexed list of old neighbours. -/
theorem sameTypeOver_orbit
    (H : HomogeneousSource S G)
    (B : FiniteInduced (X := X)) (x y : Sigma X)
    (h : SameTypeOver S B x y) :
    y ∈ orbitOver (G := G) B.vertices x := by
  letI : Finite ↥B.vertices := B.finite_vertices.to_subtype
  let f : Option (↥B.vertices) → Sigma X
    | none => x
    | some b => b.val
  let f' : Option (↥B.vertices) → Sigma X
    | none => y
    | some b => b.val
  have hcol : ∀ a b,
      taggedColour S (f a) (f b) = taggedColour S (f' a) (f' b) := by
    intro a b
    cases a with
    | none =>
      cases b with
      | none => exact h.1
      | some t => exact h.2.1 t.val t.property
    | some t =>
      cases b with
      | none => exact h.2.2 t.val t.property
      | some u => rfl
  obtain ⟨g, hg⟩ :=
    H.extends_finite_diagram (V := Option (↥B.vertices)) f f' hcol
  refine ⟨g, ?_, ?_⟩
  · change ∀ b ∈ B.vertices, g • b = b
    intro b hb
    simpa [f, f'] using (hg (some ⟨b, hb⟩))
  · simpa [f, f'] using (hg none)

end CCO.RealAction
