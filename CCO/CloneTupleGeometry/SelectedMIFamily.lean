import CCO.CloneTupleGeometry.SourceExports

/-! D05/C25: any fixed finite distinct family of actual proper FULL MI
symbols whose literal relation meet is the clone kernel. The all-MI choice
is one instance. Domain, owner injection, RAW/STRONG source instances and
mixed singleton reconstruction depend only on this fixed family's meet
equation. No optional original-F-MI assumption enters this module. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w p q
namespace CCO.CloneTupleGeometry.OwnerStage
open ParityHasse.Original TransitionClosure ExactCRT TerminalLattice
noncomputable section

/-- A once-for-all list of distinct actual MI symbols, represented by a
finite index type. The meet law concerns actual FULL relations, retaining
real equality. It is the literal permitted choice in D05/C25. -/
structure SelectedMIFamily (B : OwnerStage.{u,v,w}) (i : B.Sorts) where
  Index : Type p
  finiteIndex : Finite Index
  symbol : Index → FullCloneProperMI B.source i
  symbol_injective : Function.Injective symbol
  meet_iff : ∀ x y : CloneSAP.Carrier B.Point i,
    (∀ a, (symbol a).val x y) ↔ fullCloneKernel B.source i x y

attribute [instance] SelectedMIFamily.finiteIndex

namespace SelectedMIFamily
variable {B : OwnerStage.{u,v,w}} {i : B.Sorts}
variable (F : SelectedMIFamily.{u,v,w,p} B i)

/-- The existing all-MI construction is one allowed fixed symbol family. -/
def all (B : OwnerStage.{u,v,w}) (i : B.Sorts) : SelectedMIFamily B i where
  Index := FullCloneProperMI B.source i
  finiteIndex := inferInstance
  symbol := id
  symbol_injective := Function.injective_id
  meet_iff x y := by
    change fullCloneMIKernel B.source i x y ↔ fullCloneKernel B.source i x y
    rw [fullCloneMIKernel_eq_fullCloneKernel]

theorem kernel_le (a : F.Index) : fullCloneKernel B.source i ≤ (F.symbol a).val := by
  intro x y hxy
  exact ((F.meet_iff x y).mpr hxy) a

/-- Proper K forces at least one selected symbol; an empty list would
have FULL meet Top and collapse all infinite original owners. -/
theorem nonemptyIndex : Nonempty F.Index := by
  classical
  by_contra hn
  letI : IsEmpty F.Index := ⟨fun a => hn ⟨a⟩⟩
  have hk : (⊤ : ColourEq (CloneSAP.source B.source) i) ≤ fullCloneKernel B.source i := by
    intro x y _
    exact (F.meet_iff x y).mp (fun a => isEmptyElim a)
  exact B.clone_kernel_ne_top i (top_le_iff.mp hk)

abbrev Tuple := ∀ a : F.Index, Quotient (F.symbol a).val.val

def cloneTuple (x : CloneSAP.Carrier B.Point i) : F.Tuple :=
  fun a => Quotient.mk (F.symbol a).val.val x

def ownerTuple (x : B.Point i) : F.Tuple := F.cloneTuple (x,0)

/-- The exact selected-coordinate fibre is one actual owner fibre. -/
theorem cloneTuple_eq_iff (x y : CloneSAP.Carrier B.Point i) :
    F.cloneTuple x = F.cloneTuple y ↔ x.1 = y.1 := by
  constructor
  · intro h
    exact (F.meet_iff x y).mp (fun a => Quotient.exact (congrFun h a))
  · intro h
    funext a
    exact Quotient.sound (((F.meet_iff x y).mpr h) a)

theorem ownerTuple_eq_clone (x : B.Point i) (n : ℕ) :
    F.ownerTuple x = F.cloneTuple (x,n) :=
  (F.cloneTuple_eq_iff (x,0) (x,n)).mpr rfl

theorem ownerTuple_injective : Function.Injective F.ownerTuple := by
  intro x y h
  exact (F.cloneTuple_eq_iff (x,0) (y,0)).mp h

def Compatible (q : F.Tuple) : Prop :=
  ∀ a b : F.Index, Sum.inr ⟨rfl⟩ ∈
    originalTypedQuotientPairSpectrum (CloneSAP.source B.source)
      (F.symbol a).val (F.symbol b).val (q a) (q b)

theorem ownerTuple_compatible (x : B.Point i) : F.Compatible (F.ownerTuple x) := by
  intro a b
  exact (pure_clone_quotient_spectrum_c_iff_owner B.source i
    (F.symbol a).val (F.symbol b).val (F.kernel_le a) (F.kernel_le b) _ _).mpr
    ⟨x,rfl,rfl⟩

/-- Actual terminal class Helly applies to precisely the selected finite
family, without requiring that it contain all proper MI coordinates. -/
theorem compatible_realized (ht : B.Terminal) (q : F.Tuple) (hq : F.Compatible q) :
    ∃ x : B.Point i, F.ownerTuple x = q := by
  classical
  let E : F.Index → ExactEq (CloneSAP.source B.source)
      (CloneSAP.homogeneous B.source B.homogeneous) (CloneSAP.CCO.cco_forward B.source B.cco) i :=
    fun a => ⟨(F.symbol a).val.val,B.terminal_MI_exact ht i (F.symbol a)⟩
  let centre : F.Index → CloneSAP.Carrier B.Point i := fun a => (q a).out
  have hc (a : F.Index) : Quotient.mk (F.symbol a).val.val (centre a) = q a :=
    Quotient.out_eq _
  have hp (a b : F.Index) : ∃ x, (E a).val (centre a) x ∧ (E b).val (centre b) x := by
    obtain ⟨x,ha,hb⟩ :=
      (pure_clone_quotient_spectrum_c_iff_intersection B.source i
        (F.symbol a).val (F.symbol b).val (F.kernel_le a) (F.kernel_le b) (q a) (q b)).mp (hq a b)
    exact ⟨x,Quotient.exact ((hc a).trans ha.symm),Quotient.exact ((hc b).trans hb.symm)⟩
  obtain ⟨x,hx⟩ := exactEq_classHelly (CloneSAP.source B.source)
    (CloneSAP.homogeneous B.source B.homogeneous) (CloneSAP.CCO.cco_forward B.source B.cco) E centre hp
  refine ⟨x.1,?_⟩
  calc
    F.ownerTuple x.1 = F.cloneTuple x := F.ownerTuple_eq_clone x.1 x.2
    _ = q := by
      funext a
      exact (Quotient.sound ((F.symbol a).val.val.symm (hx a))).trans (hc a)

theorem tuple_domain (ht : B.Terminal) (q : F.Tuple) :
    (∃! x : B.Point i, F.ownerTuple x = q) ↔ F.Compatible q := by
  constructor
  · rintro ⟨x,hx,_⟩
    rw [← hx]
    exact F.ownerTuple_compatible x
  · intro hq
    obtain ⟨x,hx⟩ := F.compatible_realized ht q hq
    exact ⟨x,hx,fun y hy => F.ownerTuple_injective (hy.trans hx.symm)⟩

/-- The selected FULL meet law restricts to the actual singleton clone
diversity support, with no logical-equality atom or empty-list unit. -/
theorem diversity_meet :
    ({a : (CloneSAP.source B.source).Atom i i | ∀ k : F.Index,
      a ∈ originalEquivDiversityPalette (CloneSAP.source B.source) (F.symbol k).val} :
      (CloneSAP.source B.source).Menu i i) = {Sum.inr ⟨rfl⟩} := by
  ext a
  constructor
  · intro ha
    obtain ⟨x,y,hxy⟩ := (CloneSAP.source B.source).realized a
    have hK : fullCloneKernel B.source i x y := (F.meet_iff x y).mp (by
      intro k
      obtain ⟨p,q,hJ,hpq⟩ := ha k
      exact ((F.symbol k).val.property p q x y (hpq.trans hxy.symm)).mp hJ)
    have hindex : x.2 ≠ y.2 := by
      intro he
      have hpoint : x = y := Prod.ext hK he
      subst y
      have hh := ((CloneSAP.source B.source).colour_none_iff x x).mpr rfl
      change (CloneSAP.source B.source).colour x x = some a at hxy
      rw [hh] at hxy
      cases hxy
    have hc := (CloneSAP.source_clone_iff B.source x y).mpr ⟨hK,hindex⟩
    exact Set.mem_singleton_iff.mpr (Option.some.inj (hxy.symm.trans hc))
  · intro ha k
    have hca : a = Sum.inr ⟨rfl⟩ := Set.mem_singleton_iff.mp ha
    subst a
    exact B.clone_atom_mem_MI i (F.symbol k)

/-- Every selected symbol belongs to the actual represented B049 hidden
language. Terminality constructs its RAW word; it is no extra choice. -/
def namedCoordinate (ht : B.Terminal) (a : F.Index) :=
  B.namedMICoordinate ht i (F.symbol a)

theorem namedCoordinate_kernel (ht : B.Terminal) (a : F.Index) :
    (F.namedCoordinate ht a).val = (F.symbol a).val := rfl

theorem positive_word (ht : B.Terminal) (a : F.Index) :
    ∃ p : PositiveWord (CloneSAP.source B.source) i i,
      PositiveWord.profile (CloneSAP.source B.source) p =
        originalEquivDiversityPalette (CloneSAP.source B.source) (F.symbol a).val :=
  B.terminal_MI_positive_word ht i (F.symbol a)

theorem strong_exact (ht : B.Terminal) (a : F.Index) :
    StrongExact.Exact (CloneSAP.source B.source)
      (originalEquivDiversityPalette (CloneSAP.source B.source) (F.symbol a).val) :=
  B.terminal_MI_strong_exact ht i (F.symbol a)

/-- Right exact-product distribution over precisely the selected family. -/
theorem right_cylinders_meet (ht : B.Terminal) {j : B.Sorts}
    (a : (CloneSAP.source B.source).Atom j i) :
    ({b | ∀ k : F.Index, b ∈ (CloneSAP.source B.source).product {a}
      (originalEquivDiversityPalette (CloneSAP.source B.source) (F.symbol k).val)} :
      (CloneSAP.source B.source).Menu j i) = {a} := by
  have he := original_typed_exact_finite_right_meet
    (CloneSAP.source B.source) (CloneSAP.homogeneous B.source B.homogeneous)
    (CloneSAP.strong_amalgamation B.source B.ap) (CloneSAP.CCO.cco_forward B.source B.cco)
    {a} (fun k : F.Index => originalEquivDiversityPalette (CloneSAP.source B.source) (F.symbol k).val)
    (StrongExact.exact_singleton _ a) (F.strong_exact ht)
    (by rw [F.diversity_meet]; exact ⟨Sum.inr ⟨rfl⟩,rfl⟩)
  rw [F.diversity_meet,B.clone_strong_right] at he
  exact he.symm

variable {j : B.Sorts} (D : SelectedMIFamily.{u,v,w,q} B j)

/-- The second nonempty exact-product distribution permits independent
chosen families on both source and target sorts. -/
theorem strong_cylinder_singleton (ht : B.Terminal)
    (a : (CloneSAP.source B.source).Atom i j) :
    ({b | ∀ s : F.Index, ∀ t : D.Index,
      b ∈ (CloneSAP.source B.source).product
        (originalEquivDiversityPalette (CloneSAP.source B.source) (F.symbol s).val)
        ((CloneSAP.source B.source).product {a}
          (originalEquivDiversityPalette (CloneSAP.source B.source) (D.symbol t).val))} :
      (CloneSAP.source B.source).Menu i j) = {a} := by
  let rights (t : D.Index) := (CloneSAP.source B.source).product {a}
    (originalEquivDiversityPalette (CloneSAP.source B.source) (D.symbol t).val)
  have hr : ∀ t, StrongExact.Exact (CloneSAP.source B.source) (rights t) := by
    intro t
    exact original_typed_exact_product (CloneSAP.source B.source)
      (CloneSAP.homogeneous B.source B.homogeneous) (CloneSAP.strong_amalgamation B.source B.ap)
      (CloneSAP.CCO.cco_forward B.source B.cco) (StrongExact.exact_singleton _ a) (D.strong_exact ht t)
  have hm : ({b | ∀ t, b ∈ rights t} : (CloneSAP.source B.source).Menu i j) = {a} :=
    D.right_cylinders_meet ht a
  have he := original_typed_exact_finite_double_meet
    (CloneSAP.source B.source) (CloneSAP.homogeneous B.source B.homogeneous)
    (CloneSAP.strong_amalgamation B.source B.ap) (CloneSAP.CCO.cco_forward B.source B.cco)
    (fun s : F.Index => originalEquivDiversityPalette (CloneSAP.source B.source) (F.symbol s).val)
    rights (F.strong_exact ht) hr
    (by rw [F.diversity_meet]; exact ⟨Sum.inr ⟨rfl⟩,rfl⟩)
    (by rw [hm]; exact ⟨a,rfl⟩)
  rw [F.diversity_meet,hm,B.clone_strong_left] at he
  exact he.symm

def pairSpectrum (x : F.Tuple) (y : D.Tuple) : (CloneSAP.source B.source).Menu i j :=
  {a | ∀ s : F.Index, ∀ t : D.Index,
    a ∈ originalTypedQuotientPairSpectrum (CloneSAP.source B.source)
      (F.symbol s).val (D.symbol t).val (x s) (y t)}

/-- Actual complete mixed semantic spectra for the selected coordinates
recover the input atom, even when some hidden endpoints coincide. -/
theorem clone_pair_singleton (ht : B.Terminal)
    (x : CloneSAP.Carrier B.Point i) (y : CloneSAP.Carrier B.Point j)
    (a : (CloneSAP.source B.source).Atom i j)
    (hxy : (CloneSAP.source B.source).atomRel a x y) :
    F.pairSpectrum D (F.cloneTuple x) (D.cloneTuple y) = {a} := by
  have hc (s : F.Index) (t : D.Index) :=
    originalTypedCylinder_both_nonzero (CloneSAP.source B.source)
      (CloneSAP.homogeneous B.source B.homogeneous) (CloneSAP.strong_amalgamation B.source B.ap)
      (F.symbol s).val (D.symbol t).val
      (lt_of_le_of_ne bot_le (Ne.symm (F.symbol s).property.1))
      (lt_of_le_of_ne bot_le (Ne.symm (D.symbol t).property.1)) a x y hxy
  calc
    _ = {b | ∀ s : F.Index, ∀ t : D.Index,
      b ∈ (CloneSAP.source B.source).product
        (originalEquivDiversityPalette (CloneSAP.source B.source) (F.symbol s).val)
        ((CloneSAP.source B.source).product {a}
          (originalEquivDiversityPalette (CloneSAP.source B.source) (D.symbol t).val))} := by
      ext b
      constructor
      · intro hb s t
        rw [← hc s t]
        exact hb s t
      · intro hb s t
        change b ∈ originalTypedQuotientPairSpectrum (CloneSAP.source B.source)
          (F.symbol s).val (D.symbol t).val
          (Quotient.mk (F.symbol s).val.val x) (Quotient.mk (D.symbol t).val.val y)
        rw [hc s t]
        exact hb s t
    _ = {a} := F.strong_cylinder_singleton D ht a

theorem original_pair_singleton (ht : B.Terminal)
    (x : B.Point i) (y : B.Point j) (a : B.source.Atom i j)
    (hxy : B.source.atomRel a x y) :
    F.pairSpectrum D (F.ownerTuple x) (D.ownerTuple y) = {Sum.inl a} :=
  F.clone_pair_singleton D ht (x,0) (y,0) (Sum.inl a)
    ((CloneSAP.colour_old_iff B.source (x,0) (y,0) a).mpr hxy)

end SelectedMIFamily

namespace SelectedMIFamily
variable {B : OwnerStage.{u,v,w}} {i : B.Sorts}
variable (F : SelectedMIFamily.{u,v,w,p} B i) (D : SelectedMIFamily.{u,v,w,q} B i)

/-- Equal visible owners use distinct real clones. This works even for
two different selected symbol families on the same original sort. -/
theorem equal_owner_singleton (ht : B.Terminal) (x : B.Point i) :
    F.pairSpectrum D (F.ownerTuple x) (D.ownerTuple x) = {Sum.inr ⟨rfl⟩} := by
  have hc := F.clone_pair_singleton D ht (x,0) (x,1) (Sum.inr ⟨rfl⟩)
    ((CloneSAP.source_clone_iff B.source (x,0) (x,1)).mpr ⟨rfl,Nat.zero_ne_one⟩)
  rw [← F.ownerTuple_eq_clone x 0,← D.ownerTuple_eq_clone x 1] at hc
  exact hc

end SelectedMIFamily

namespace SelectedMIFamily
variable {B : OwnerStage.{u,v,w}} {i j : B.Sorts}
variable (F : SelectedMIFamily.{u,v,w,p} B i) (D : SelectedMIFamily.{u,v,w,q} B j)

/-- Semantic fine-colour readout for the selected-family QF consumer.
The same-sort visible equality case satisfies no old diversity atom. -/
theorem original_colour_iff (ht : B.Terminal)
    (x : B.Point i) (y : B.Point j) (a : B.source.Atom i j) :
    Sum.inl a ∈ F.pairSpectrum D (F.ownerTuple x) (D.ownerTuple y) ↔ B.source.atomRel a x y := by
  constructor
  · intro ha
    cases hc : B.source.colour x y with
    | none =>
      have he := (B.source.colour_none_iff x y).mp hc
      have hij : i = j := congrArg Sigma.fst he
      subst j
      have hxy : x = y := eq_of_heq (Sigma.mk.inj he).2
      subst y
      rw [F.equal_owner_singleton D ht x] at ha
      cases Set.mem_singleton_iff.mp ha
    | some b =>
      rw [F.original_pair_singleton D ht x y b hc] at ha
      have hab : a = b := Sum.inl.inj (Set.mem_singleton_iff.mp ha)
      subst a
      exact hc
  · intro ha
    rw [F.original_pair_singleton D ht x y a ha]
    rfl

end SelectedMIFamily
end
end CCO.CloneTupleGeometry.OwnerStage
