import CCO.CloneTupleGeometry.OptionalKernelMI
import CCO.CloneTupleGeometry.SourceExports
import CCO.CloneTupleGeometry.SelectedFamilyQF

/-! Optional N10 conclusion: after the actual original-F-MI kernel proof,
ONE genuine represented proper MI coordinate may be chosen. Its quotient
is literally the original owner type, and its complete mixed spectrum
already gives the actual one-coordinate fine-colour/equality readout. The
all-MI family is not asserted to have cardinal one. Optional ancestry is
confined to this file and OptionalKernelMI/OriginalFMIClosure. -/
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w t z
namespace CCO.CloneTupleGeometry
open APCharacter APCharacter.Towers ParityHasse.Original
open TerminalPowers TransitionClosure TerminalLattice
noncomputable section
namespace OwnerStage
variable (B : OwnerStage.{u,v,w})

/-- One K-class is exactly one actual owner; this is a genuine quotient
bijection, independent of any selection from the all-MI family. -/
def kernelOwnerEquiv (i : B.Sorts) : B.Point i ≃ Quotient (fullCloneKernel B.source i).val where
  toFun x := Quotient.mk _ (x,0)
  invFun := Quotient.lift Prod.fst (fun _ _ h => h)
  left_inv _ := rfl
  right_inv q := Quotient.inductionOn q (fun _ => Quotient.sound rfl)

/-- The FULL clone kernel has precisely the clone diversity atom as its
support; its real diagonal is retained only in the FULL relation. -/
theorem kernel_diversity_singleton (i : B.Sorts) :
    originalEquivDiversityPalette (CloneSAP.source B.source) (fullCloneKernel B.source i) =
      {Sum.inr ⟨rfl⟩} := by
  ext a
  constructor
  · rintro ⟨x,y,hK,hcol⟩
    have hx : x.1 = y.1 := hK
    have hn : x.2 ≠ y.2 := by
      intro he
      have heq : x = y := Prod.ext hx he
      subst y
      have hz := ((CloneSAP.source B.source).colour_none_iff x x).mpr rfl
      rw [hz] at hcol
      cases hcol
    have hc := (CloneSAP.source_clone_iff B.source x y).mpr ⟨hx,hn⟩
    exact Set.mem_singleton_iff.mpr (Option.some.inj (hcol.symm.trans hc))
  · intro ha
    have he := Set.mem_singleton_iff.mp ha
    subst a
    obtain ⟨x⟩ := B.source.nonemptySort i
    exact ⟨(x,0),(x,1),rfl,
      (CloneSAP.source_clone_iff B.source (x,0) (x,1)).mpr ⟨rfl,Nat.zero_ne_one⟩⟩

/-- ONE mixed K coordinate has the exact actual atom singleton, including
hidden equality and the same-owner clone marker. This is proved from the
actual source cylinder theorem and actual clone endpoint multiplication. -/
theorem kernel_coordinate_pair_singleton {i j : B.Sorts}
    (x : CloneSAP.Carrier B.Point i) (y : CloneSAP.Carrier B.Point j)
    (a : (CloneSAP.source B.source).Atom i j)
    (hxy : (CloneSAP.source B.source).atomRel a x y) :
    originalTypedQuotientPairSpectrum (CloneSAP.source B.source)
      (fullCloneKernel B.source i) (fullCloneKernel B.source j)
      ⟦x⟧ ⟦y⟧ = {a} := by
  rw [originalTypedCylinder_both_nonzero (CloneSAP.source B.source)
    (CloneSAP.homogeneous B.source B.homogeneous)
    (CloneSAP.strong_amalgamation B.source B.ap)
    (fullCloneKernel B.source i) (fullCloneKernel B.source j)
    (lt_of_le_of_ne bot_le (Ne.symm (fullCloneKernel_ne_bot B.source i)))
    (lt_of_le_of_ne bot_le (Ne.symm (fullCloneKernel_ne_bot B.source j))) a x y hxy]
  rw [B.kernel_diversity_singleton,B.kernel_diversity_singleton,
    B.clone_strong_right,B.clone_strong_left]

/-- The literal one-coordinate QF spectrum formula defines every original
fine relation. Visible equality satisfies no old diversity formula. -/
theorem kernel_coordinate_fine_readout {i j : B.Sorts}
    (q : B.Point i) (r : B.Point j) (a : B.source.Atom i j) :
    (QuotientPairQF.membershipFormula (CloneSAP.source B.source)
      (fullCloneKernel B.source i) (fullCloneKernel B.source j) (Sum.inl a)).eval
      (B.kernelOwnerEquiv i q) (B.kernelOwnerEquiv j r) ↔ B.source.atomRel a q r := by
  rw [QuotientPairQF.membershipFormula_eval (CloneSAP.source B.source)
    (CloneSAP.homogeneous B.source B.homogeneous)]
  constructor
  · rintro ⟨x,y,hx,hy,hcol⟩
    have hqx : q = x.1 := by
      have he := Quotient.exact hx
      exact he.symm
    have hry : r = y.1 := by
      have he := Quotient.exact hy
      exact he.symm
    rw [hqx,hry]
    exact (CloneSAP.colour_old_iff B.source x y a).mp hcol
  · intro hcol
    exact ⟨(q,0),(r,0),rfl,rfl,(CloneSAP.colour_old_iff B.source (q,0) (r,0) a).mpr hcol⟩

/-- The diagonal in the one-coordinate visible domain returns the clone
marker via two distinct actual clones, never an equality diversity atom. -/
theorem kernel_coordinate_equal_readout {i : B.Sorts} (q : B.Point i) :
    originalTypedQuotientPairSpectrum (CloneSAP.source B.source)
      (fullCloneKernel B.source i) (fullCloneKernel B.source i)
      (B.kernelOwnerEquiv i q) (B.kernelOwnerEquiv i q) = {Sum.inr ⟨rfl⟩} := by
  have he := B.kernel_coordinate_pair_singleton (q,0) (q,1) (Sum.inr ⟨rfl⟩)
    ((CloneSAP.source_clone_iff B.source (q,0) (q,1)).mpr ⟨rfl,Nat.zero_ne_one⟩)
  have hq : (Quotient.mk (fullCloneKernel B.source i).val (q,1)) =
      B.kernelOwnerEquiv i q := Quotient.sound rfl
  rw [hq] at he
  exact he

end OwnerStage
namespace OptionalFMI
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable (ap : AgeAP S) (cco : SemanticCCO.{0,v,v,w} S)
variable (countable : ∀ i : Unit, Countable M) (infinite : ∀ i : Unit, Infinite M)

/-- Actual C75 auxiliary source consumer: one MAY CHOOSE the singleton
family (K) of actual represented proper FULL MI coordinates. Its quotient
is the whole owner sort, with literal QF fine-colour and equality readout.
This does not claim that the generic all-MI index has only one element. -/
theorem actual_one_coordinate_geometry
    (hF : InfIrred (FinitePackets.Geometry.sigma S H (⊥ : ColourEq S ())))
    {B : OwnerStage.{0,v,w}}
    (h : History OwnerStage.Next (initialOwnerStage S H ap cco countable infinite) B)
    (ht : B.Terminal) (i : B.Sorts) :
    ∃ J : OriginalNamedHiddenCoordinate (CloneSAP.source B.source)
        (CloneSAP.homogeneous B.source B.homogeneous) i,
      J.val = fullCloneKernel B.source i ∧
      ∃ eta : B.Point i ≃ Quotient J.val.val, ∀ q : B.Point i,
        originalTypedQuotientPairSpectrum (CloneSAP.source B.source) J.val J.val
          (eta q) (eta q) = {Sum.inr ⟨rfl⟩} := by
  let J : FullCloneProperMI B.source i := ⟨fullCloneKernel B.source i,
    fullCloneKernel_ne_bot B.source i,
    terminal_cloneKernel_infIrred S H ap cco countable infinite hF h ht i⟩
  exact ⟨B.namedMICoordinate ht i J,rfl,B.kernelOwnerEquiv i,
    fun q => B.kernel_coordinate_equal_readout q⟩

/-- A simultaneous literal singleton-coordinate choice on ALL final sorts,
with actual mixed one-coordinate QF fine readout and visible equality.
The choice is exactly K in every sort, not the all-MI index family. -/
theorem actual_one_coordinate_source
    (hF : InfIrred (FinitePackets.Geometry.sigma S H (⊥ : ColourEq S ())))
    {B : OwnerStage.{0,v,w}}
    (h : History OwnerStage.Next (initialOwnerStage S H ap cco countable infinite) B)
    (ht : B.Terminal) :
    ∃ coordinate : ∀ i : B.Sorts,
        OriginalNamedHiddenCoordinate (CloneSAP.source B.source)
          (CloneSAP.homogeneous B.source B.homogeneous) i,
      ∃ eta : ∀ i : B.Sorts, B.Point i ≃ Quotient (coordinate i).val.val,
        (∀ i, (coordinate i).val = fullCloneKernel B.source i) ∧
        (∀ {i j : B.Sorts} (q : B.Point i) (r : B.Point j) (a : B.source.Atom i j),
          (QuotientPairQF.membershipFormula (CloneSAP.source B.source)
            (coordinate i).val (coordinate j).val (Sum.inl a)).eval (eta i q) (eta j r) ↔
              B.source.atomRel a q r) ∧
        (∀ {i : B.Sorts} (q : B.Point i),
          originalTypedQuotientPairSpectrum (CloneSAP.source B.source)
            (coordinate i).val (coordinate i).val (eta i q) (eta i q) = {Sum.inr ⟨rfl⟩}) := by
  let J (i : B.Sorts) : FullCloneProperMI B.source i := ⟨fullCloneKernel B.source i,
    fullCloneKernel_ne_bot B.source i,
    terminal_cloneKernel_infIrred S H ap cco countable infinite hF h ht i⟩
  let coordinate (i : B.Sorts) := B.namedMICoordinate ht i (J i)
  let eta (i : B.Sorts) : B.Point i ≃ Quotient (coordinate i).val.val := B.kernelOwnerEquiv i
  exact ⟨coordinate,eta,fun _ => rfl,
    fun q r a => B.kernel_coordinate_fine_readout q r a,
    fun q => B.kernel_coordinate_equal_readout q⟩

/-- The actual permitted singleton family in the arbitrary-family API.
Only the chosen index is Unit; no assertion about the all-MI index is made. -/
def selectedKernelFamily
    (hF : InfIrred (FinitePackets.Geometry.sigma S H (⊥ : ColourEq S ())))
    {B : OwnerStage.{0,v,w}}
    (h : History OwnerStage.Next (initialOwnerStage S H ap cco countable infinite) B)
    (ht : B.Terminal) (i : B.Sorts) : B.SelectedMIFamily i where
  Index := Unit
  finiteIndex := inferInstance
  symbol _ := ⟨fullCloneKernel B.source i,fullCloneKernel_ne_bot B.source i,
    terminal_cloneKernel_infIrred S H ap cco countable infinite hF h ht i⟩
  symbol_injective := fun _ _ _ => Subsingleton.elim _ _
  meet_iff _ _ := ⟨fun h => h (),fun h _ => h⟩

/-- C75: the arbitrary selected-family domain/cylinder pipeline applies
literally to the once-for-all family (K_s), of cardinal ONE on every sort. -/
theorem actual_selected_singleton_family
    (hF : InfIrred (FinitePackets.Geometry.sigma S H (⊥ : ColourEq S ())))
    {B : OwnerStage.{0,v,w}}
    (h : History OwnerStage.Next (initialOwnerStage S H ap cco countable infinite) B)
    (ht : B.Terminal) :
    ∃ family : ∀ i : B.Sorts, OwnerStage.SelectedMIFamily.{0,v,w,0} B i,
      ∀ i, Nat.card (family i).Index = 1 ∧
        (∀ a, ((family i).symbol a).val = fullCloneKernel B.source i) ∧
        ∀ q : (family i).Tuple,
          (∃! x : B.Point i, (family i).ownerTuple x = q) ↔ (family i).Compatible q := by
  refine ⟨selectedKernelFamily S H ap cco countable infinite hF h ht,?_⟩
  intro i
  exact ⟨by simp [selectedKernelFamily],fun _ => rfl,
    (selectedKernelFamily S H ap cco countable infinite hF h ht i).tuple_domain ht⟩

/-- A genuine receiving use of C75: repeat the ENTIRE selected-family QF
and simultaneous finite hidden reconstruction pipeline for precisely (K).
Every chosen index has one element, all pair colours use the actual QF
readout, and the reconstructed finite owner table/chart is independent of
the one whole hidden realization. -/
theorem actual_singleton_hidden_reconstruction
    (hF : InfIrred (FinitePackets.Geometry.sigma S H (⊥ : ColourEq S ())))
    {B : OwnerStage.{0,v,w}}
    (h : History OwnerStage.Next (initialOwnerStage S H ap cco countable infinite) B)
    (ht : B.Terminal) {V : Type z} (D : OwnerStage.FiniteHidden.Object B V)
    (member : OwnerStage.FiniteHidden.Member D) :
    let families := selectedKernelFamily S H ap cco countable infinite hF h ht
    (∀ i, Nat.card (families i).Index = 1 ∧
      ∀ a, ((families i).symbol a).val = fullCloneKernel B.source i) ∧
    (∀ {i j : B.Sorts} (x : B.Point i) (y : B.Point j) (a : B.source.Atom i j),
      OwnerStage.SelectedMIFamily.QF.readoutEval (families i) (families j) (Sum.inl a)
        ((families i).ownerTuple x) ((families j).ownerTuple y) ↔ B.source.atomRel a x y) ∧
    ∃ e : OwnerStage.FiniteHidden.Realization D,
      Function.Injective (OwnerStage.SelectedMIFamily.QF.visiblePoint families D e ht) ∧
      Age.Realized B.source (Age.zeroMask B.source)
        (OwnerStage.SelectedMIFamily.QF.visibleTable families D e ht) ∧
      ∀ f : OwnerStage.FiniteHidden.Realization D,
        OwnerStage.SelectedMIFamily.QF.visibleTable families D e ht =
          OwnerStage.SelectedMIFamily.QF.visibleTable families D f ht ∧
        OwnerStage.SelectedMIFamily.QF.visibleChart families D e ht =
          OwnerStage.SelectedMIFamily.QF.visibleChart families D f ht := by
  let families := selectedKernelFamily S H ap cco countable infinite hF h ht
  refine ⟨fun i => ⟨by simp [families,selectedKernelFamily],fun _ => rfl⟩,?_,?_⟩
  · exact fun x y a => OwnerStage.SelectedMIFamily.QF.original_colour_readout
      (families _) (families _) ht x y a
  · exact OwnerStage.SelectedMIFamily.QF.finite_hidden_reconstruction families D ht member

end OptionalFMI
end
end CCO.CloneTupleGeometry
