import CCO.TypedOrbitFrames.ExactColouredOrbit
import CCO.StabilizerHomogeneity

/-!
# Source11 T03: exact old types are actual original-fixer coordinate orbits

One finite original partial isomorphism extends by the original source
homogeneity. It fixes the entire real base and sends the one real root to
the chosen realisation. Thus T02 gives infinitely many actual quotient
values under the SAME original pointwise stabilizer, without assuming
hidden homogeneity or identifying its full automorphism group with G.
-/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Original CCO.TerminalLattice CCO.TransitionClosure
open CCO.UnaryTermsReturn CCO.RealClosure.Bounds

universe u v w z r
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {B : Type z} [Finite B] (base : B ↪ Sigma X)
variable {i : ι} (q : X i)
variable {G : Type r} [Group G] [∀ j : ι, MulAction G (X j)]

/-- The actual original-real-base fixer orbit of one actual J-class.
No independent action on hidden vertices is supplied as a premise. -/
def originalRealBaseCoordinateOrbit (J : ColourEq S i) :
    Set (Quotient J.val) :=
  {c | ∃ g : G, g ∈ RealAction.pointwiseStabilizer (Set.range base) ∧
    Quotient.mk J.val (g • q) = c}

/-- The complete one-point type is realised by one original automorphism
fixing the whole real base, including when the point lies in the base. -/
theorem original_exact_type_iff_original_fixer
    (H : HomogeneousSource S G) (x : X i) :
    (∀ d : B, S.colour x (base d).2 = S.colour q (base d).2) ↔
      ∃ g : G, g ∈ RealAction.pointwiseStabilizer (Set.range base) ∧
        g • q = x := by
  constructor
  · intro hSpokes
    let D : FiniteInduced (X := X) :=
      ⟨Set.range base, Set.finite_range base⟩
    have hLeft : ∀ b ∈ D.vertices,
        taggedColour S (⟨i,q⟩ : Sigma X) b =
          taggedColour S (⟨i,x⟩ : Sigma X) b := by
      rintro b ⟨d,rfl⟩
      exact congrArg (fun a : Option (S.Atom i (base d).1) =>
        (⟨i,(base d).1,a⟩ : Σ j : ι, Σ k : ι, Option (S.Atom j k)))
        (hSpokes d).symm
    have hType : RealAction.SameTypeOver S D
        (⟨i,q⟩ : Sigma X) (⟨i,x⟩ : Sigma X) := by
      refine ⟨?_,hLeft,?_⟩
      · have hq := (S.colour_none_iff q q).mpr rfl
        have hx := (S.colour_none_iff x x).mpr rfl
        simp only [taggedColour,hq,hx]
      · intro b hb
        rw [original_actual_tagged_colour_converse S b ⟨i,q⟩,
          original_actual_tagged_colour_converse S b ⟨i,x⟩,
          hLeft b hb]
    obtain ⟨g,hg,hgx⟩ := RealAction.sameTypeOver_orbit S H D
      (⟨i,q⟩ : Sigma X) (⟨i,x⟩ : Sigma X) hType
    refine ⟨g,hg,?_⟩
    simpa only [Sigma.smul_mk,Sigma.mk.injEq,heq_eq_eq,true_and] using hgx
  · rintro ⟨g,hg,rfl⟩ d
    have hFix : g • (base d).2 = (base d).2 := by
      have h := hg (base d) ⟨d,rfl⟩
      change (⟨(base d).1,g • (base d).2⟩ : Sigma X) =
        ⟨(base d).1,(base d).2⟩ at h
      simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using h
    simpa only [hFix] using S.colourInvariant_of_homogeneous H g q (base d).2

/-- Equality of actual value sets, rather than only an injection from a
conditional orbit provider. Both directions use the original action. -/
theorem original_exact_type_classes_eq_original_fixer_orbit
    (H : HomogeneousSource S G) (J : ColourEq S i) :
    originalExactTypeClasses S base q J =
      originalRealBaseCoordinateOrbit S base q (G := G) J := by
  ext c
  constructor
  · rintro ⟨x,hType,hx⟩
    obtain ⟨g,hg,hgx⟩ :=
      (original_exact_type_iff_original_fixer S base q H x).mp hType
    exact ⟨g,hg,(congrArg (Quotient.mk J.val) hgx).trans hx⟩
  · rintro ⟨g,hg,hq⟩
    exact ⟨g • q,
      (original_exact_type_iff_original_fixer S base q H (g • q)).mpr
        ⟨g,hg,rfl⟩,hq⟩

/-- T02 expressed as the genuine original-group quotient orbit over a
finite complete original real base. This is the hidden case of TOS. -/
theorem original_unforced_real_base_coordinate_orbit_infinite
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (nr2 : Selectors.OriginalNR2 S)
    (J : OriginalNamedHiddenCoordinate S H i)
    (hunforced :
      originalCompletedNamedHiddenNode S H J (Quotient.mk J.val.val q)
        ∉ originalCompletedRealBaseClosure S H sap nr2 (Set.range base)) :
    (originalRealBaseCoordinateOrbit S base q (G := G) J.val).Infinite := by
  rw [← original_exact_type_classes_eq_original_fixer_orbit S base q H J.val]
  exact original_typed_exact_coloured_orbit_infinitude S base q H sap cco nr2
    J hunforced

end CCO.TypedOrbitFrames
