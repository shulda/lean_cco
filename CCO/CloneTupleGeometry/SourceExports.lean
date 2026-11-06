import CCO.CloneTupleGeometry.FiniteHiddenReconstruction
import CCO.CloneSAP.ExactKernel

/-! The three source-dependent selected B060 exports, C20/C34/C52.
All terminal source, full-MI, RAW/STRONG, marked-age and finite hidden
realization duties are discharged by the actual preceding constructions.
The independent typed distributivity export lives in IndependentExports.
There is no optional original-F-MI ancestor and no Ramsey/EPPA premise. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w z
namespace CCO.CloneTupleGeometry
open APCharacter APCharacter.Towers ParityHasse.Original
open TransitionClosure TerminalPowers QuotientTransport
noncomputable section

namespace OwnerStage
variable (B : OwnerStage.{u,v,w})

/-- The selected FULL MI is a genuine proper MI in the whole ambient
group-invariant lattice used by B049, not just in an exact sublattice. -/
theorem fullMI_original_proper (i : B.Sorts) (J : FullCloneProperMI B.source i) :
    ProperMeetIrreducible
      (originalColourEqAsInvEq (CloneSAP.source B.source)
        (CloneSAP.homogeneous B.source B.homogeneous) J.val) := by
  let e := originalFullColourEqInvEqOrderIso (CloneSAP.source B.source)
    (CloneSAP.homogeneous B.source B.homogeneous) (i := i)
  change ProperMeetIrreducible (e J.val)
  constructor
  · intro htop
    apply J.property.2.ne_top
    have h := congrArg e.symm htop
    simpa only [OrderIso.symm_apply_apply,OrderIso.map_top] using h
  · intro L N h
    have hmeet : e.symm L ⊓ e.symm N = J.val := by
      have he := congrArg e.symm h.symm
      rw [e.symm.map_inf] at he
      simpa only [OrderIso.symm_apply_apply] using he
    rcases J.property.2.2 hmeet with he | he
    · left
      have hh := congrArg e he
      simpa only [OrderIso.apply_symm_apply] using hh.symm
    · right
      have hh := congrArg e he
      simpa only [OrderIso.apply_symm_apply] using hh.symm

/-- Explicit actual membership in the accepted represented hidden language.
The underlying FULL kernel is literally J; its RAW word is constructed by
the terminal source theorem, never supplied as another provider premise. -/
def namedMICoordinate (ht : B.Terminal) (i : B.Sorts)
    (J : FullCloneProperMI B.source i) :
    OriginalNamedHiddenCoordinate (CloneSAP.source B.source)
      (CloneSAP.homogeneous B.source B.homogeneous) i :=
  ⟨J.val,lt_of_le_of_ne bot_le (Ne.symm J.property.1),B.fullMI_original_proper i J,
    RealClosure.Bounds.terminal_one_raw_word (CloneSAP.source B.source)
      (CloneSAP.homogeneous B.source B.homogeneous) (B.terminal_sortNR2 ht i) J.val⟩

theorem namedMICoordinate_kernel (ht : B.Terminal) (i : B.Sorts)
    (J : FullCloneProperMI B.source i) : (B.namedMICoordinate ht i J).val = J.val := rfl
end OwnerStage

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)]

/-- `lem:ramsey-clone-stability`, C20: ORIGINAL countably infinite
homogeneous AP+HOM CCO hypotheses construct an actual finite safe phase
history. Its endpoint is canonical owner-times-N, retains infinite owner
types, and its SAME owner reduct is reasonable, reduct-surjective and
precompact. Every clone kernel is nonzero, proper and FULL RAW exact. -/
theorem ramsey_clone_stability
    (H : HomogeneousSource S G) (ap : AgeAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (countable : ∀ i, Countable (X i)) (infinite : ∀ i, Infinite (X i)) :
    ∃ B : OwnerStage.{u,v,w},
      ∃ history : History OwnerStage.Next (initialOwnerStage S H ap cco countable infinite) B,
        B.Terminal ∧
        history.length + B.potential ≤ (initialOwnerStage S H ap cco countable infinite).potential ∧
        ∃ reduct : UnaryReduct S B.source,
          ∃ unary : UnaryTransition
            (initialOwnerStage S H ap cco countable infinite).finiteAge B.finiteAge,
            unary.forget = reduct.forget ∧
            ∀ i : B.Sorts, Infinite (B.Point i) ∧
              fullCloneKernel B.source i ≠ ⊥ ∧ fullCloneKernel B.source i ≠ ⊤ ∧
              RawWord.relation (CloneSAP.source B.source) (CloneSAP.kernelWord B.source i) =
                (fullCloneKernel B.source i).val.r := by
  obtain ⟨B,h,ht,hbound,reduct,unary,hforget⟩ :=
    actual_owner_finite_safe_terminalisation S H ap cco countable infinite
  exact ⟨B,h,ht,hbound,reduct,unary,hforget,fun i =>
    ⟨B.infinite i,fullCloneKernel_ne_bot B.source i,B.clone_kernel_ne_top i,
      CloneSAP.kernelWord_relation B.source i⟩⟩

variable (B : OwnerStage.{u,v,w})

/-- `lem:ramsey-mi-domain`, C34: a fixed nonempty finite family of ACTUAL
represented proper FULL MI coordinates identifies owners with exactly the
compatible tuples. The explicit quantifier-free formula has the same
meaning for any actual whole finite hidden member, including orphans. -/
theorem ramsey_mi_domain (ht : B.Terminal) (i : B.Sorts) :
    Finite (FullCloneProperMI B.source i) ∧ Nonempty (FullCloneProperMI B.source i) ∧
    Function.Injective (originalOwnerMITuple B.source i) ∧
    (∀ J : FullCloneProperMI B.source i,
      (B.namedMICoordinate ht i J).val = J.val) ∧
    (∀ q : FullCloneMITuple B.source i,
      (∃! x : B.Point i, originalOwnerMITuple B.source i x = q) ↔ B.TupleCompatible i q) ∧
    (∀ a : OwnerStage.TupleQF.Assignment B i,
      (OwnerStage.TupleQF.domainFormula B i).eval a ↔
        ∃! x : B.Point i, ∀ J,
          a J = QuotientPairQF.hiddenPoint (CloneSAP.source B.source) J.val
            (originalOwnerMITuple B.source i x J)) ∧
    (∀ {V : Type z} (D : OwnerStage.FiniteHidden.Object B V), OwnerStage.FiniteHidden.Member D →
      ∃ e : OwnerStage.FiniteHidden.Realization D,
        Function.Injective (e.visiblePoint ht) ∧
        Age.Realized B.source (Age.zeroMask B.source) (e.visibleTable ht) ∧
        ∀ (j : B.Sorts) (q : D.VisibleTuple j), ∃! x : B.Point j, ∀ J,
          e.point (q.val J) = QuotientPairQF.hiddenPoint (CloneSAP.source B.source) J.val
            (originalOwnerMITuple B.source j x J)) := by
  refine ⟨inferInstance,B.clone_MI_nonempty i,originalOwnerMITuple_injective B.source i,
    B.namedMICoordinate_kernel ht i,B.terminal_tuple_domain i ht,
    OwnerStage.TupleQF.domainFormula_unique_owner B i ht,?_⟩
  rintro V D ⟨e⟩
  exact ⟨e,e.visiblePoint_injective ht,e.visibleTable_realized ht,fun j q => e.owner_exists ht q⟩

/-- `lem:ramsey-singleton-recovery`, C52: full mixed spectra recover the
literal original fine atom; visible equality separately returns c. The
finite quantifier-free old-colour formula reconstructs the ENTIRE finite
visible object through one whole hidden realization, and its actual owner
table/chart and every pair colour are independent of that realization. -/
theorem ramsey_singleton_recovery (ht : B.Terminal) :
    (∀ {i j : B.Sorts} (q : B.Point i) (r : B.Point j) (a : B.source.Atom i j),
      B.source.atomRel a q r →
        B.tuplePairSpectrum (originalOwnerMITuple B.source i q)
          (originalOwnerMITuple B.source j r) = {Sum.inl a}) ∧
    (∀ {i : B.Sorts} (q : B.Point i),
      B.tuplePairSpectrum (originalOwnerMITuple B.source i q)
        (originalOwnerMITuple B.source i q) = {Sum.inr ⟨rfl⟩}) ∧
    (∀ {i j : B.Sorts} (q : B.Point i) (r : B.Point j) (a : B.source.Atom i j),
      B.spectrumReadoutEval i (Sum.inl a) (originalOwnerMITuple B.source i q)
        (originalOwnerMITuple B.source j r) ↔ B.source.atomRel a q r) ∧
    (∀ {V : Type z} (D : OwnerStage.FiniteHidden.Object B V), OwnerStage.FiniteHidden.Member D →
      ∃ e : OwnerStage.FiniteHidden.Realization D,
        Function.Injective (e.visiblePoint ht) ∧
        Age.Realized B.source (Age.zeroMask B.source) (e.visibleTable ht) ∧
        (∀ {i j : B.Sorts} (a : B.source.Atom i j) (q : D.VisibleTuple i) (r : D.VisibleTuple j),
          D.colourReadout a q r ↔ B.source.atomRel a (e.owner ht q) (e.owner ht r)) ∧
        ∀ f : OwnerStage.FiniteHidden.Realization D,
          e.visibleTable ht = f.visibleTable ht ∧ e.visibleChart ht = f.visibleChart ht ∧
          ∀ {i j : B.Sorts} (q : D.VisibleTuple i) (r : D.VisibleTuple j),
            B.source.colour (e.owner ht q) (e.owner ht r) =
              B.source.colour (f.owner ht q) (f.owner ht r)) := by
  refine ⟨fun q r a h => B.terminal_original_pair_singleton ht q r a h,
    fun q => B.terminal_equal_owner_singleton ht q,
    fun q r a => B.original_colour_readout _ ht q r a,?_⟩
  rintro V D ⟨e⟩
  exact ⟨e,e.visiblePoint_injective ht,e.visibleTable_realized ht,
    fun a q r => e.colour_readout ht a q r,
    fun f => ⟨e.visibleTable_independent f ht,e.visibleChart_independent f ht,
      fun q r => e.colour_independent f ht q r⟩⟩

end
end CCO.CloneTupleGeometry
