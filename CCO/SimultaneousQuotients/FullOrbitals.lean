import CCO.SimultaneousQuotients.FullAut

/-! A named quotient colour is exactly a full-Aut pair orbit. The old group
is transitive inside each named colour; full automorphisms cannot merge names.
This is equality of pair orbits, not surjectivity of the original group onto
full Aut, and supplies no coherent or homomorphic section. -/

universe u v w t
namespace CCO.SimultaneousQuotients
namespace FullAut
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

def PairOrbit (p q p' q' : Sigma X) : Prop :=
  ∃ g : Aut S, g.val p = p' ∧ g.val q = q'

variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G)
include H

/-- The full binary automorphism group has precisely the same named pair
orbits as the original homogeneous action, on every typed ordered pair. -/
theorem pairOrbit_iff_colour {i j : ι} (x x' : X i) (y y' : X j) :
    PairOrbit S ⟨i,x⟩ ⟨j,y⟩ ⟨i,x'⟩ ⟨j,y'⟩ ↔
      S.colour x y = S.colour x' y' := by
  constructor
  · rintro ⟨g, hgx, hgy⟩
    have h := (g.property.2 (taggedColour S ⟨i,x⟩ ⟨j,y⟩) ⟨i,x⟩ ⟨j,y⟩).mpr rfl
    change taggedColour S (g.val ⟨i,x⟩) (g.val ⟨j,y⟩) =
      taggedColour S ⟨i,x⟩ ⟨j,y⟩ at h
    rw [hgx, hgy] at h
    have hc : S.colour x' y' = S.colour x y := by
      simpa only [taggedColour, Sigma.mk.injEq, heq_eq_eq, true_and] using h
    exact hc.symm
  · intro hc
    obtain ⟨g,hgx,hgy⟩ := S.pair_homogeneous_of_homogeneous H x x' y y' hc
    refine ⟨motion S H g, ?_, ?_⟩
    · exact congrArg (Sigma.mk i) hgx
    · exact congrArg (Sigma.mk j) hgy

end FullAut

open RawExact
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{u,v,max u v,w} S)
variable (J : ∀ i, Setoid (X i)) (E : ∀ i, NonemptyExact S i i)
variable (represents : ∀ i, evaluate S (E i).words = (J i).r)
variable [∀ i, Countable (X i)]
include cco

/-- Actual original-G quotient pair orbits equal actual FULL quotient-Aut
pair orbits. The two GROUPS themselves are not identified. -/
theorem original_orbit_iff_full_orbit :
    letI : ∀ i, MulAction G (Carrier J i) := action S H J E represents
    ∀ {i j} (x x' : Carrier J i) (y y' : Carrier J j),
    GroupActions.orbital (G := G) x y x' y' ↔
      FullAut.PairOrbit (source S H J E represents) ⟨i,x⟩ ⟨j,y⟩ ⟨i,x'⟩ ⟨j,y'⟩ := by
  letI : ∀ i, MulAction G (Carrier J i) := action S H J E represents
  intro i j x x' y y'
  rw [FullAut.pairOrbit_iff_colour (source S H J E represents)
    (homogeneous S H J E represents cco) x x' y y']
  exact (actual_colours S H J E represents x y x' y').symm

end CCO.SimultaneousQuotients
