import CCO.HereditaryHiddenOrbits.FullHidden

/-!
# The exact source12 theorem and named HO equation

The source group is the FULL original typed permutation group, obtained
from the given original homogeneity theorem. Its actual hidden action and
faithful inclusion are constructed; full hidden Aut remains a separate
group. All conclusions concern exactly the actual named represented sorts.
-/

universe u v w r
namespace CCO.HereditaryHiddenOrbits.Source
open CCO.ParityHasse.Original CCO.TypedOrbitFrames CCO.UnaryFreshFrames
noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)
variable (hCover : ∀ i : ι, OriginalAllFullCoversInfinite S (i := i))

/-- The original FULL old group, on the actual interpreted carrier.
Faithfulness follows because the original real sorts are retained. -/
theorem full_original_inclusion_injective :
    let HF := TerminalPowers.full_homogeneous S H
    Function.Injective (originalCompletedMotionHom S HF sap (terminalNR2 S hCover)) :=
  original_completed_full_group_inclusion_injective S
    (TerminalPowers.full_homogeneous S H) sap (terminalNR2 S hCover)

/-- Source equation (HO), for the original FULL Aut(M), every finite
actual closed hidden base and the SAME actual off-base vertex. -/
theorem typed_hereditary_hidden_orbits_equation
    (cco : SemanticCCO.{u,v,max u v,w} S) :
    let HF := TerminalPowers.full_homogeneous S H
    ∀ (A : Set (Carrier S HF)), A.Finite → (hidden S HF sap hCover).Closed A →
      ∀ x : Carrier S HF, x ∉ A → (OriginalOrbit S HF A x).Infinite :=
  original_hidden_closed_orbit_infinite S (TerminalPowers.full_homogeneous S H)
    sap hCover cco

/-- Source lemma: original FULL-group HO and, for arbitrary finite
hidden parameters, FULL hidden acl=dcl=finite term closure. No actual
hidden homogeneity, hereditary SAP or new source provider is assumed. -/
theorem typed_hereditary_hidden_orbits
    (cco : SemanticCCO.{u,v,max u v,w} S) :
    let HF := TerminalPowers.full_homogeneous S H
    (∀ (A : Set (Carrier S HF)), A.Finite → (hidden S HF sap hCover).Closed A →
      ∀ x : Carrier S HF, x ∉ A → (OriginalOrbit S HF A x).Infinite) ∧
    (∀ (T : Set (Carrier S HF)), T.Finite →
      Acl (hidden S HF sap hCover).Aut T = (hidden S HF sap hCover).closure T ∧
      Dcl (hidden S HF sap hCover).Aut T = (hidden S HF sap hCover).closure T ∧
      ((hidden S HF sap hCover).closure T).Finite) := by
  refine ⟨typed_hereditary_hidden_orbits_equation S H sap hCover cco,?_⟩
  intro T hT
  exact ⟨full_acl_eq_closure S (TerminalPowers.full_homogeneous S H) sap hCover cco T hT,
    full_dcl_eq_closure S (TerminalPowers.full_homogeneous S H) sap hCover cco T hT,
    locally_finite S (TerminalPowers.full_homogeneous S H) sap hCover T hT⟩

end
end CCO.HereditaryHiddenOrbits.Source
