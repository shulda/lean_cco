import CCO.PairSafeSplit.Strong.ExtraIdentity
import CCO.PairSafeSplit.Strong.WordFamily
import CCO.PairSafeSplit.SAP.Gates
import CCO.PairSafeSplit.Full.EPP
import CCO.StrongExact.PaletteNonempty

/-! B047 C56–C59. Actual STRONG phase primality. A possible RAW identity
is dealt with by the independently proved original-SAP obstruction, not
silently removed from the FULL EPP hypothesis. -/

set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace CCO.PairSafeSplit.Strong
open APCharacter RigidGroupoid.Geometry RigidGroupoid.Phase
open ParityHasse.Original
noncomputable section
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable {H : HomogeneousSource S G} {C : ExactCalculus S} {r : ι} {A : Kernel S r}

def sheetPalette (P : SourcePhase S H C A) (b c : Reached S A) (δ : Bit) : S.Menu b.val c.val :=
  {a | ∀ x y, S.colour x y = some a → Full.Sheet P b c δ x y}

theorem sheet_gate_zero (P : SourcePhase S H C A) (b : Reached S A) (δ : Bit)
    (x y : X b.val) (hK : (Reached.kernel H C b).rel x y)
    (h : Full.Sheet P b b δ x y) : δ = 0 := by
  letI := Reached.groupoid H C (A := A)
  obtain ⟨R,hR,hχ⟩ := h
  have he := R.eq_of_common_real_pair H (Arrow.id _) hR hK
  exact hχ.symm.trans ((congrArg P.character.value he).trans (P.character.map_id b))

/-- C57 in the literal actual maximal-character construction. -/
theorem phase_one_no_identity (P : SourcePhase S H C A)
    (sap : AgeSAP S) (cco : SemanticCCO.{u,v,max u v,w} S)
    (b : Reached S A) (D : X b.val → X b.val → Prop)
    (hD : ParityHasse.Relative.Exact S D) (hDiv : ∃ x y, D x y ∧ x ≠ y)
    (δ : Bit) (hδ : δ ≠ 0)
    (hSheet : ∀ x y, x ≠ y → D x y → Full.Sheet P b b δ x y) :
    ∀ x, ¬ D x x := by
  apply no_extra_identity S H sap cco D hD hDiv
    (SAP.reachedKernelEq P b) (Reached.kernel H C b).exact (SAP.reached_kernel_ne_bot P sap b)
  intro x y hxy hK
  by_contra hn
  exact hδ (sheet_gate_zero P b δ x y hK (hSheet x y hn hxy))

/-- Every actual nonempty STRONG common profile confined to one deterministic
sheet has an individual profile in that sheet. Empty families are included. -/
theorem typed_epp (P : SourcePhase S H C A) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S) (b c : Reached S A)
    (ps : List (PositiveWord S b.val c.val)) (δ : Bit)
    (hne : (StrongExact.present S ps).Nonempty)
    (hSheet : StrongExact.present S ps ⊆ sheetPalette P b c δ) :
    ∃ p ∈ ps, PositiveWord.profile S p ⊆ sheetPalette P b c δ := by
  classical
  letI := Reached.groupoid H C (A := A)
  let ds := rawFamily S H sap ps
  have hRaw : TRel.Nonempty (fun x y => ∀ d ∈ ds, RawExact.evaluate S d.words x y) :=
    rawFamily_nonempty S H sap ps hne
  have fullSheet : ∀ x y, (∀ d ∈ ds, RawExact.evaluate S d.words x y) →
      Full.Sheet P b c δ x y := by
    intro x y hxy
    cases hc : S.colour x y with
    | some a =>
      exact hSheet ((rawFamily_guard S H sap ps hc).mp hxy) x y hc
    | none =>
      have he := (S.colour_none_iff x y).mp hc
      have hbc : b = c := Subtype.ext (congrArg Sigma.fst he)
      subst c
      have hpt : x = y := by
        simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using he
      subst y
      by_cases hz : δ = 0
      · subst δ
        exact ⟨Arrow.id _,(Reached.kernel H C b).setoid.refl x,P.character.map_id b⟩
      · let D : X b.val → X b.val → Prop := fun u v => ∀ d ∈ ds, RawExact.evaluate S d.words u v
        have hD : ParityHasse.Relative.Exact S D :=
          ⟨RawExact.exactFamilyMeet S ds hRaw,RawExact.exactFamilyMeet_relation S ds hRaw⟩
        have hDiv : ∃ u v, D u v ∧ u ≠ v := by
          obtain ⟨a,ha⟩ := hne
          obtain ⟨u,v,hc⟩ := S.realized a
          exact ⟨u,v,(rawFamily_guard S H sap ps hc).mpr ha,by
            intro he
            subst v
            have hn := (S.colour_none_iff u u).mpr rfl
            rw [hn] at hc
            cases hc⟩
        have hDsheet : ∀ u v, u ≠ v → D u v → Full.Sheet P b b δ u v := by
          intro u v hne huv
          obtain ⟨a,hc⟩ := S.some_colour_of_ne u v (by
            intro he
            exact hne (by simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using he))
          exact hSheet ((rawFamily_guard S H sap ps hc).mp huv) u v hc
        exact False.elim (phase_one_no_identity P sap cco b D hD hDiv δ hz hDsheet x hxy)
  obtain ⟨d,hd,hds⟩ := Full.typed_epp P cco b c ds δ hRaw fullSheet
  obtain ⟨p,hp,hpd⟩ := List.mem_map.mp hd
  refine ⟨p,hp,?_⟩
  intro a ha x y hc
  apply hds x y
  rw [← hpd,rawPresentation_relation]
  exact (profile_iff_represented S H sap p hc).mp ha

/-- The strong empty-family case never selects a nonexistent word. -/
theorem top_not_one_sheet (P : SourcePhase S H C A) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S) (b c : Reached S A) (δ : Bit) :
    ¬ (Set.univ ⊆ sheetPalette P b c δ) := by
  intro h
  obtain ⟨a⟩ := StrongExact.palette_nonempty_of_SAP S H sap b.val c.val
  have hn : (StrongExact.present S ([] : List (PositiveWord S b.val c.val))).Nonempty :=
    ⟨a,by simp [StrongExact.present]⟩
  obtain ⟨p,hp,_⟩ := typed_epp P sap cco b c [] δ hn (by
    rw [StrongExact.present_nil]
    exact h)
  exact List.not_mem_nil hp

end
end CCO.PairSafeSplit.Strong
