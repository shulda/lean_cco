import CCO.TypedOrbitFrames.RealBaseClosure
import CCO.TransitionClosure.OriginalNamedRawInverse

/-!
# Source11 QT4: an unforced actual spoke has an external STRONG atom

If the complete two-edge STRONG fork through an old anchor were contained
in the original kernel J, its equality-inclusive atomic RAW fork would
also lie in J: equal endpoints use reflexivity and distinct endpoints
have their actual diversity colour in that same STRONG product.

The resulting genuine named old atomic quotient transition has a named
converse transition. On the actual spoke, projection of the old anchor
followed by this converse primitive is LITERALLY the J-projection of x.
This is a path in the complete interpreted unary language and contradicts
being outside the FULL real-base closure. Original SAP and FULL NR2
discharge the nonidentity represented target gate through the accepted
named transition definitions; no hidden source SAP is assumed.
-/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Original CCO.TerminalLattice
open CCO.TransitionClosure CCO.UnaryTermsReturn

universe u v w t

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ k : ι, MulAction G (X k)]

/-- Source11 QT4 for EACH actual old diversity spoke. Its strong fork
profile cannot be contained in J's diversity palette if the actual
J-coordinate is outside the FULL named unary closure of the old base.
The old anchor is allowed to have any original named sort. -/
theorem original_unforced_actual_spoke_profile_exits
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    (D : Set (Sigma X))
    {i : ι} (J : OriginalNamedHiddenCoordinate S H i) (x : X i)
    (hunforced :
      originalCompletedNamedHiddenNode S H J (Quotient.mk J.val.val x)
        ∉ originalCompletedRealBaseClosure S H sap nr2 D)
    {j : ι} (d : X j) (hd : (⟨j,d⟩ : Sigma X) ∈ D)
    (a : S.Atom i j) (hSpoke : S.atomRel a x d) :
    ¬ S.product ({a} : S.Menu i j) ({S.conv a} : S.Menu j i) ⊆
      originalEquivDiversityPalette S J.val := by
  intro hInside
  have hKernel : ∀ u v : X i, ∀ y : X j,
      S.atomRel a u y → S.atomRel a v y → J.val u v := by
    intro u v y huy hvy
    by_cases huv : u = v
    · subst v
      exact J.val.val.refl u
    · have hTagged : (⟨i,u⟩ : Sigma X) ≠ ⟨i,v⟩ := by
        intro he
        exact huv (eq_of_heq (Sigma.mk.inj he).2)
      obtain ⟨c,hc⟩ := S.some_colour_of_ne u v hTagged
      have hFork : c ∈
          S.product ({a} : S.Menu i j) ({S.conv a} : S.Menu j i) :=
        ⟨a,rfl,S.conv a,rfl,u,y,v,huy,
          (S.colour_swap v y a).mp hvy,hc⟩
      obtain ⟨u',v',hJ,hColour⟩ := hInside hFork
      exact (J.val.property u' v' u v (hColour.trans hc.symm)).mp hJ
  let atomSymbol : OriginalNamedAtomicTransitionSymbol S H i j :=
    ⟨⟨J,a⟩,hKernel⟩
  let rawSymbol : OriginalNamedRawTransitionSymbol S H i j :=
    originalNamedAtomicSymbol_asRaw S H atomSymbol
  let target : OriginalNamedHiddenCoordinate S H j :=
    originalNamedRawTransitionSymbol_target S H sap nr2 rawSymbol
  let inverse : OriginalNamedRawTransitionSymbol S H j i :=
    originalNamedRawTransitionSymbol_converse S H sap nr2 rawSymbol
  have hTarget :
      originalNamedRawTransitionSymbol_target S H sap nr2 inverse = J :=
    originalNamedRawTransitionSymbol_converse_target_name
      S H sap nr2 rawSymbol
  have hReverse : inverse.val.2.val.val d x := by
    change S.atomRel a x d
    exact hSpoke
  have hValue :
      originalNamedRawTransitionSymbol_function S H sap nr2 inverse
          (Quotient.mk target.val.val d) =
        Quotient.mk
          (originalNamedRawTransitionSymbol_target
            S H sap nr2 inverse).val.val x :=
    (originalNamedRawTransitionSymbol_transport S H inverse).quotientEquiv_edge
      hReverse
  have hNode :
      originalCompletedNamedHiddenNode S H
          (originalNamedRawTransitionSymbol_target S H sap nr2 inverse)
          (originalNamedRawTransitionSymbol_function S H sap nr2 inverse
            (Quotient.mk target.val.val d)) =
        originalCompletedNamedHiddenNode S H J
          (Quotient.mk J.val.val x) := by
    rw [hValue]
    exact congrArg (fun K : OriginalNamedHiddenCoordinate S H i =>
      originalCompletedNamedHiddenNode S H K (Quotient.mk K.val.val x)) hTarget
  have hReach : OriginalCompletedNamedReachable S H sap nr2
      (.inl (⟨j,d⟩ : Sigma X))
      (originalCompletedNamedHiddenNode S H J (Quotient.mk J.val.val x)) := by
    rw [← hNode]
    exact .step (.step (.refl _) (.projection target d))
      (.rawTransition inverse (Quotient.mk target.val.val d))
  apply hunforced
  apply Set.mem_iUnion.mpr
  refine ⟨(⟨j,d⟩ : Sigma X), ?_⟩
  apply Set.mem_iUnion.mpr
  exact ⟨hd,hReach⟩

end CCO.TypedOrbitFrames
