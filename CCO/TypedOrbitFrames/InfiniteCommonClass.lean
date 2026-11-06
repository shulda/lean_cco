import CCO.TypedOrbitFrames.CommonFibreAvoidance
import CCO.TypedOrbitFrames.FullMIMeetPrime
import CCO.PairSafeSplit.Infinity.TypeFibres

/-!
# Source11 T04: the genuine common class is infinite

For each nonidentity old equivalence choose a different point of its
class. The complete finite base of all these actual anchors omits the
root. Old SAP gives its infinite stabilizer orbit; fixing each anchor
keeps that SAME orbit in every old equivalence class. This is the finite
family content of the old-SAP monolith argument, with the empty family
handled by the same empty anchor base. All other T04 source providers
are the already proved actual Helly, FULL meet-prime and FULL-cover-index
theorems and the one-action simultaneous avoidance theorem.
-/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Original CCO.RealClosure.Bounds

universe u v w r
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ j : ι, MulAction G (X j)]

/-- A finite intersection of actual nonidentity old equivalences has
an infinite class. Both distinct anchor values may coincide; the whole
actual finite anchor SET is fixed at once. -/
theorem original_nonidentity_finite_meet_class_infinite
    (H : HomogeneousSource S G) (sap : AgeSAP S) {i : ι} {m : Nat}
    (E : Fin m → ColourEq S i) (hE : ∀ j, ⊥ < E j) (x : X i) :
    {y : X i | originalActualMeetEquivalence S E x y}.Infinite := by
  classical
  choose anchor hAnchorClass hAnchorNe using
    fun j => PairSafeSplit.Infinity.class_has_other S H (E j) (hE j) x
  let tags : Fin m → Sigma X := fun j => ⟨i,anchor j⟩
  let D : FiniteInduced (X := X) := ⟨Set.range tags,Set.finite_range tags⟩
  have hxD : (⟨i,x⟩ : Sigma X) ∉ D.vertices := by
    rintro ⟨j,hj⟩
    have hax : anchor j = x := by
      simpa only [tags,Sigma.mk.injEq,heq_eq_eq,true_and] using hj
    exact hAnchorNe j hax.symm
  have hInf := RealAction.infinite_stabilizer_orbit_of_SAP S H sap D ⟨i,x⟩ hxD
  intro hFinite
  apply hInf
  apply (hFinite.image (Sigma.mk i)).subset
  rintro _ ⟨g,hg,rfl⟩
  refine ⟨g • x,?_,rfl⟩
  intro j
  have hFix : g • anchor j = anchor j := by
    have h := hg (tags j) ⟨j,rfl⟩
    change (⟨i,g • anchor j⟩ : Sigma X) = ⟨i,anchor j⟩ at h
    simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using h
  have hMoved := colourInvariant_groupInvariant S H (E j).property g x (anchor j)
    (hAnchorClass j)
  rw [hFix] at hMoved
  exact (E j).val.trans (hAnchorClass j) ((E j).val.symm hMoved)

/-- The full meet is still genuinely nonidentity; no fake identity
coordinate can replace the common class of the source theorem. -/
theorem original_nonidentity_finite_meet_ne_bot
    (H : HomogeneousSource S G) (sap : AgeSAP S) {i : ι} {m : Nat}
    (E : Fin m → ColourEq S i) (hE : ∀ j, ⊥ < E j) :
    originalActualMeetEquivalence S E ≠ ⊥ := by
  intro hBot
  obtain ⟨x⟩ := S.nonemptySort i
  have hInf := original_nonidentity_finite_meet_class_infinite S H sap E hE x
  rw [hBot] at hInf
  exact hInf (by simpa only [ColourEq.bot_apply,Set.setOf_eq_eq_singleton']
    using Set.finite_singleton x)

/-- T04's actual common class exists and is ONE INFINITE full-meet
class. Exact old Helly supplies the common point; old SAP supplies its
infinitude, including the literal empty family and arbitrary named sort. -/
theorem original_terminal_actual_common_class_infinite
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S) {i : ι} (nr2 : SortNR2 S i)
    {m : Nat} (E : Fin m → ColourEq S i) (c : Fin m → X i)
    (hE : ∀ j, ⊥ < E j)
    (hPair : ∀ j k, ∃ x : X i, E j (c j) x ∧ E k (c k) x) :
    ∃ x : X i, x ∈ originalActualClassFibre S E c ∧
      originalActualClassFibre S E c =
        {y : X i | originalActualMeetEquivalence S E x y} ∧
      (originalActualClassFibre S E c).Infinite := by
  obtain ⟨x,hx⟩ := original_terminal_actual_pairwise_class_helly S H cco nr2 E c hPair
  have hEq := original_actual_class_fibre_eq_full_meet_class S E c x hx
  refine ⟨x,hx,hEq,?_⟩
  rw [hEq]
  exact original_nonidentity_finite_meet_class_infinite S H sap E hE x

/-- The proper FULL MI dichotomy in this ONE common actual fibre.
The unforced case uses the literal standing infinite FULL cover indices,
including Top covers. The forced case selects one EXISTING input class. -/
theorem original_terminal_actual_mi_fibre_dichotomy
    (H : HomogeneousSource S G) (cco : SemanticCCO.{u,v,max u v,w} S)
    {i : ι} (nr2 : SortNR2 S i) (hCover : OriginalAllFullCoversInfinite S (i := i))
    {m : Nat} (E : Fin m → ColourEq S i) (c : Fin m → X i)
    (hPair : ∀ j k, ∃ x : X i, E j (c j) x ∧ E k (c k) x)
    (J : ColourEq S i) (hJ : J ≠ ⊤) (hMI : ExactCRT.FiniteOrder.BinaryMeetIrreducible J) :
    (originalActualMeetEquivalence S E ≤ J →
      ∃ j, E j ≤ J ∧ ∀ x y : X i,
        x ∈ originalActualClassFibre S E c → y ∈ originalActualClassFibre S E c → J x y) ∧
    (¬ originalActualMeetEquivalence S E ≤ J →
      Infinite {q : Quotient J.val // ∃ y : X i,
        y ∈ originalActualClassFibre S E c ∧ Quotient.mk J.val y = q}) := by
  constructor
  · exact original_terminal_common_fibre_forced_J S H cco nr2 E c J hJ hMI
  · intro hUnforced
    obtain ⟨x,hx,hInf⟩ := original_terminal_common_fibre_unforced_classes_infinite
      S H cco nr2 E c hPair hCover J hUnforced
    exact hInf

end CCO.TypedOrbitFrames
