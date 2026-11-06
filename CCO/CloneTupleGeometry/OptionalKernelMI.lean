import CCO.CloneTupleGeometry.OwnerEquivalenceDescent
import CCO.CloneTupleGeometry.OwnerFiniteBaseTower
import CCO.CloneTupleGeometry.TerminalPacketSeparation
import CCO.CloneTupleGeometry.OriginalFMIClosure
import Mathlib.Tactic.FinCases

/-! Optional N10 original-F-MI branch. A hypothetical transverse pair of
FULL terminal clone equivalences gives an off-base owner corner algebraic
over two actual owners. The genuine finite safe history preserves that
finite-base algebraicity. Original C19/C07 closure puts the corner in an
original finite packet, while terminal packet separation permits only one
owner of that packet in the final sort. Thus the actual clone kernel is
proper FULL MI. No premise here is an arbitrary unary-preservation callback.
This file is forbidden ancestry of the four main geometry exports. -/
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe v w t
namespace CCO.CloneTupleGeometry.OptionalFMI
open APCharacter APCharacter.Towers ParityHasse.Original TerminalPowers
noncomputable section

private def twoAnchorBase (D : OwnerStage.{0,v,w}) {i : D.Sorts}
    (x y : D.Point i) (hne : x ≠ y) : Fin 2 ↪ Sigma D.Point where
  toFun a := if a = 0 then ⟨i,x⟩ else ⟨i,y⟩
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

/-- A genuine transverse FULL pair defines a unique off-base owner corner
in the actual owner language. Its whole pointwise-base orbit is finite. -/
private theorem corner_type_finite (D : OwnerStage.{0,v,w}) {i : D.Sorts}
    (U V : ColourEq (CloneSAP.source D.source) i)
    (hU : fullCloneKernel D.source i ≤ U) (hV : fullCloneKernel D.source i ≤ V)
    (hUV : U ⊓ V = fullCloneKernel D.source i)
    (x y z : D.Point i) (hxy : x ≠ y)
    (hxz : D.ownerEquivalence i U x z) (hyz : D.ownerEquivalence i V y z) :
    (ownerTypeOver D.source (twoAnchorBase D x y hxy) z).Finite := by
  rw [ownerTypeOver_eq_orbit D.source D.homogeneous]
  apply (Set.finite_singleton z).subset
  rintro q ⟨g,hg,hgq⟩
  have hgx := hg (0 : Fin 2)
  have hgy := hg (1 : Fin 2)
  change (⟨i,g • x⟩ : Sigma D.Point) = ⟨i,x⟩ at hgx
  change (⟨i,g • y⟩ : Sigma D.Point) = ⟨i,y⟩ at hgy
  have hfx : g • x = x := eq_of_heq (Sigma.mk.inj hgx).2
  have hfy : g • y = y := eq_of_heq (Sigma.mk.inj hgy).2
  have hxq : D.ownerEquivalence i U x q := by
    have hp := ((D.ownerEquivalence i U).property (g • x) (g • z) x z
      (fullAut_colour D.source g i i x z)).mpr hxz
    simpa only [hfx,hgq] using hp
  have hyq : D.ownerEquivalence i V y q := by
    have hp := ((D.ownerEquivalence i V).property (g • y) (g • z) y z
      (fullAut_colour D.source g i i y z)).mpr hyz
    simpa only [hfy,hgq] using hp
  have hzq : (D.ownerEquivalence i U ⊓ D.ownerEquivalence i V) z q :=
    ⟨(D.ownerEquivalence i U).val.trans ((D.ownerEquivalence i U).val.symm hxz) hxq,
      (D.ownerEquivalence i V).val.trans ((D.ownerEquivalence i V).val.symm hyz) hyq⟩
  rw [← D.ownerEquivalence_inf,hUV,D.ownerEquivalence_cloneKernel] at hzq
  exact hzq.symm

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable (ap : AgeAP S) (cco : SemanticCCO.{0,v,v,w} S)
variable (countable : ∀ i : Unit, Countable M) (infinite : ∀ i : Unit, Infinite M)

/-- Actual optional C71–C75: original F-MI plus the GENUINE safe history
implies proper FULL MI of every final clone kernel. Original algebraicity,
actual finite-base preservation and terminal packet separation are all
discharged internally, not hidden in stronger hypotheses. -/
theorem terminal_cloneKernel_infIrred
    (hF : InfIrred (FinitePackets.Geometry.sigma S H (⊥ : ColourEq S ())))
    {D : OwnerStage.{0,v,w}}
    (h : History OwnerStage.Next (initialOwnerStage S H ap cco countable infinite) D)
    (ht : D.Terminal) (i : D.Sorts) : InfIrred (fullCloneKernel D.source i) := by
  classical
  let R : Towers.UnaryReduct S D.source := OwnerStage.historyReduct h
  have originalInfinite : Infinite M := infinite ()
  letI := originalInfinite
  refine ⟨?_,?_⟩
  · intro hmax
    exact D.clone_kernel_ne_top i (hmax.eq_top)
  · intro U V hUV
    by_contra hn
    push Not at hn
    have hKU : fullCloneKernel D.source i ≤ U := hUV ▸ inf_le_left
    have hKV : fullCloneKernel D.source i ≤ V := hUV ▸ inf_le_right
    have hUn : D.ownerEquivalence i U ≠ ⊥ := D.ownerEquivalence_ne_bot i U hKU hn.1
    have hVn : D.ownerEquivalence i V ≠ ⊥ := D.ownerEquivalence_ne_bot i V hKV hn.2
    obtain ⟨z⟩ := D.source.nonemptySort i
    obtain ⟨x,hxz,hUx⟩ := D.owner_equivalence_class_nontrivial i _ hUn z
    obtain ⟨y,hyz,hVy⟩ := D.owner_equivalence_class_nontrivial i _ hVn z
    have hxy : x ≠ y := by
      intro he
      have hh : (D.ownerEquivalence i U ⊓ D.ownerEquivalence i V) x z :=
        ⟨hUx,he ▸ hVy⟩
      rw [← D.ownerEquivalence_inf,hUV,D.ownerEquivalence_cloneKernel] at hh
      exact hxz hh
    let base := twoAnchorBase D x y hxy
    have hfinal : (ownerTypeOver D.source base z).Finite :=
      corner_type_finite D U V hKU hKV hUV x y z hxy hUx hVy
    have hold := (OwnerStage.history_ownerTypesFinite h base z).mp hfinal
    let oldBase : Fin 2 → M := fun a => if a = 0 then R.point i x else R.point i y
    let A : Finset M := {R.point i x,R.point i y}
    have hbase : R.project ∘ base = (fun a => (⟨(),oldBase a⟩ : Sigma (fun _ : Unit => M))) := by
      funext a
      fin_cases a <;> cases R.parent i <;> rfl
    change (ownerTypeOver S (R.project ∘ base) (R.point i z)).Finite at hold
    rw [hbase] at hold
    have hp : R.parent i = () := Subsingleton.elim _ _
    change (ownerTypeOver S (fun a => (⟨(),oldBase a⟩ : Sigma (fun _ : Unit => M)))
      (i := R.parent i) (R.point i z)).Finite at hold
    rw [hp] at hold
    have covers (a : M) : a ∈ A ↔ ∃ j, oldBase j = a := by
      simp only [A,Finset.mem_insert,Finset.mem_singleton]
      constructor
      · rintro (rfl | rfl)
        · exact ⟨0,rfl⟩
        · exact ⟨1,rfl⟩
      · rintro ⟨j,rfl⟩
        fin_cases j <;> simp [oldBase]
    have horbit := ownerTypeOver_finset_orbit_eq S
      (DirectOwnerClosure.full_homogeneous S H) oldBase A covers (R.point i z)
    rw [horbit] at hold
    have halg : R.point i z ∈ DirectOwnerClosure.algebraicClosure
        (DirectOwnerClosure.FullAut S) A := hold
    rw [original_all_finite_base_packet_closure S H cco hF A] at halg
    obtain ⟨a,ha,haz⟩ := halg
    rcases (show a = R.point i x ∨ a = R.point i y by
      simpa only [A,Finset.mem_insert,Finset.mem_singleton] using ha) with he | he
    · subst a
      exact hxz (terminal_original_sigma_packet S D R i H ht x z haz)
    · subst a
      exact hyz (terminal_original_sigma_packet S D R i H ht y z haz)

end
end CCO.CloneTupleGeometry.OptionalFMI
