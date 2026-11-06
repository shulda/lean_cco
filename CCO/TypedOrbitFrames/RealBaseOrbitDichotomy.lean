import CCO.TypedOrbitFrames.CompletedOriginalAction
import CCO.TypedOrbitFrames.RealBaseCoordinateOrbits
import CCO.StabilizerSAP

/-!
# Source11 PG-ACL/TOS on the entire actual real/hidden carrier

All full unary closure points are fixed by the original pointwise
stabilizer. Every point outside that closure has an infinite orbit:
old real SAP gives the real case and the proved exact-coloured T02
theorem gives every genuinely represented hidden quotient case.
-/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Original CCO.TerminalLattice CCO.TransitionClosure
open CCO.UnaryTermsReturn CCO.QuotientTransport CCO.RealClosure.Bounds

universe u v w r
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ j : ι, MulAction G (X j)]

theorem original_completed_hidden_node_injective
    (H : HomogeneousSource S G) {i : ι}
    (J : OriginalNamedHiddenCoordinate S H i) :
    Function.Injective (originalCompletedNamedHiddenNode S H J) := by
  intro q t h
  have hv := congrArg Subtype.val (Sum.inr.inj h)
  simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using hv

/-- Fixing the source of a genuine unary primitive fixes its unique
actual value. All three actual symbol classes are discharged here. -/
theorem original_completed_named_step_fixed
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) (g : G)
    {a b : OriginalCompletedNamedCarrier S H}
    (h : OriginalCompletedNamedStep S H sap nr2 a b)
    (hFix : originalCompletedNamedAct S H g a = a) :
    originalCompletedNamedAct S H g b = b := by
  cases h with
  | projection J x =>
      have hx : g • x = x := by
        have hv := Sum.inl.inj hFix
        change (⟨_,g • x⟩ : Sigma X) = ⟨_,x⟩ at hv
        simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using hv
      change originalCompletedNamedHiddenNode S H J
        (Quotient.mk J.val.val (g • x)) = _
      rw [hx]
  | upward D E hDE q =>
      have hq : (originalColourEqAsInvEq S H D.val).act g q = q :=
        original_completed_hidden_node_injective S H D hFix
      have hv := (original_completed_upward_equivariant S H g D E hDE q).symm
      exact congrArg (originalCompletedNamedHiddenNode S H E)
        (hv.trans (congrArg (Quot.mapRight hDE) hq))
  | rawTransition a q =>
      have hq : (originalColourEqAsInvEq S H a.val.1.val).act g q = q :=
        original_completed_hidden_node_injective S H a.val.1 hFix
      have hv := (original_completed_raw_equivariant S H sap nr2 g a q).symm
      exact congrArg (originalCompletedNamedHiddenNode S H
          (originalNamedRawTransitionSymbol_target S H sap nr2 a))
        (hv.trans (congrArg
          (originalNamedRawTransitionSymbol_function S H sap nr2 a) hq))

theorem original_completed_named_reachable_fixed
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) (g : G)
    {a b : OriginalCompletedNamedCarrier S H}
    (h : OriginalCompletedNamedReachable S H sap nr2 a b)
    (hFix : originalCompletedNamedAct S H g a = a) :
    originalCompletedNamedAct S H g b = b := by
  induction h with
  | refl => exact hFix
  | step h e ih => exact original_completed_named_step_fixed S H sap nr2 g e ih

/-- The actual completed orbit under precisely the ORIGINAL real-base
pointwise stabilizer; no full-hidden-Aut identification is asserted. -/
def originalCompletedRealBaseOrbit (H : HomogeneousSource S G)
    (D : Set (Sigma X)) (x : OriginalCompletedNamedCarrier S H) :
    Set (OriginalCompletedNamedCarrier S H) :=
  {y | ∃ g : G, g ∈ RealAction.pointwiseStabilizer D ∧
    originalCompletedNamedAct S H g x = y}

/-- Every value of every actual named unary term on D is fixed. -/
theorem original_completed_real_base_closure_fixed
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) (D : Set (Sigma X))
    (x : OriginalCompletedNamedCarrier S H)
    (hx : x ∈ originalCompletedRealBaseClosure S H sap nr2 D)
    (g : G) (hg : g ∈ RealAction.pointwiseStabilizer D) :
    originalCompletedNamedAct S H g x = x := by
  obtain ⟨p,hp⟩ := Set.mem_iUnion.mp hx
  obtain ⟨hD,hPath⟩ := Set.mem_iUnion.mp hp
  apply original_completed_named_reachable_fixed S H sap nr2 g hPath
  exact congrArg Sum.inl (hg p hD)

theorem original_completed_real_base_closure_orbit_singleton
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) (D : Set (Sigma X))
    (x : OriginalCompletedNamedCarrier S H)
    (hx : x ∈ originalCompletedRealBaseClosure S H sap nr2 D) :
    originalCompletedRealBaseOrbit S H D x = {x} := by
  ext y
  constructor
  · rintro ⟨g,hg,hgy⟩
    exact hgy.symm.trans
      (original_completed_real_base_closure_fixed S H sap nr2 D x hx g hg)
  · intro hy
    have hyx : y = x := hy
    subst y
    exact ⟨1,Subgroup.one_mem _,original_completed_named_act_one S H x⟩

/-- Source11 TOS: EVERY actual completed vertex outside the FULL unary
closure of a finite complete original real base has infinite original
fixer orbit, including literal empty bases and genuine orphan classes. -/
theorem original_completed_outside_real_base_orbit_infinite
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (nr2 : Selectors.OriginalNR2 S) (D : Set (Sigma X)) (hD : D.Finite)
    (x : OriginalCompletedNamedCarrier S H)
    (hx : x ∉ originalCompletedRealBaseClosure S H sap nr2 D) :
    (originalCompletedRealBaseOrbit S H D x).Infinite := by
  classical
  cases x with
  | inl x =>
      have hxD : x ∉ D := by
        intro hxD
        apply hx
        exact Set.mem_iUnion.mpr ⟨x,Set.mem_iUnion.mpr
          ⟨hxD,OriginalCompletedNamedReachable.refl _⟩⟩
      have hReal := RealAction.infinite_stabilizer_orbit_of_SAP S H sap
        (⟨D,hD⟩ : FiniteInduced (X := X)) x hxD
      have hImage :
          (Sum.inl '' RealAction.orbitOver (G := G) D x :
            Set (OriginalCompletedNamedCarrier S H)).Infinite :=
        hReal.image Sum.inl_injective.injOn
      apply Set.Infinite.mono ?_ hImage
      rintro y ⟨z,⟨g,hg,hgz⟩,rfl⟩
      exact ⟨g,hg,congrArg Sum.inl hgz⟩
  | inr x =>
      obtain ⟨i,J,q,hxJ⟩ := original_completed_hidden_value_has_named_witness S H x
      rw [hxJ] at hx ⊢
      induction q using Quotient.inductionOn with
      | _ q =>
        letI : Finite D := hD.to_subtype
        let base : D ↪ Sigma X := ⟨Subtype.val,Subtype.val_injective⟩
        have hBase : Set.range base = D := Subtype.range_coe
        have hInf := original_unforced_real_base_coordinate_orbit_infinite
          S base q H sap cco nr2 J (hBase.symm ▸ hx)
        have hImage := hInf.image (original_completed_hidden_node_injective S H J).injOn
        apply Set.Infinite.mono ?_ hImage
        rintro y ⟨c,⟨g,hg,hgc⟩,rfl⟩
        exact ⟨g,hBase ▸ hg,congrArg (originalCompletedNamedHiddenNode S H J) hgc⟩

/-- Source11 PG-ACL as equality of actual sets. Closure points are
fixed, and all other points have infinite ORIGINAL real-base orbits. -/
theorem original_completed_real_base_finite_orbit_iff_closure
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (nr2 : Selectors.OriginalNR2 S) (D : Set (Sigma X)) (hD : D.Finite)
    (x : OriginalCompletedNamedCarrier S H) :
    (originalCompletedRealBaseOrbit S H D x).Finite ↔
      x ∈ originalCompletedRealBaseClosure S H sap nr2 D := by
  classical
  constructor
  · intro hFinite
    by_contra hx
    exact original_completed_outside_real_base_orbit_infinite
      S H sap cco nr2 D hD x hx hFinite
  · intro hx
    rw [original_completed_real_base_closure_orbit_singleton S H sap nr2 D x hx]
    exact Set.finite_singleton x

end CCO.TypedOrbitFrames
