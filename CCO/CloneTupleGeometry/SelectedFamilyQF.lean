import CCO.CloneTupleGeometry.SelectedMIFamily
import CCO.CloneTupleGeometry.FiniteHiddenReconstruction

/-! Quantifier-free geometry for ANY fixed finite distinct proper FULL
MI subfamily whose literal meet is K. The all-MI family is only one
possible choice. The same finite cylinder/equality formulas reconstruct
all valid tuples of one whole finite hidden member simultaneously, with
the actual visible source structure independent of its realization. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w p q z
namespace CCO.CloneTupleGeometry.OwnerStage.SelectedMIFamily
open ParityHasse.Original APCharacter
noncomputable section
variable {B : OwnerStage.{u,v,w}} {i : B.Sorts}
variable (F : SelectedMIFamily.{u,v,w,p} B i)

namespace QF

abbrev Assignment := F.Index → QuotientPairQF.HiddenPoint (CloneSAP.source B.source)

inductive Formula where
  | truth : Formula
  | sort (a : F.Index) : Formula
  | pair (a b : F.Index)
      (test : QuotientPairQF.Formula (CloneSAP.source B.source) (F.symbol a).val (F.symbol b).val) : Formula
  | conj (a b : Formula) : Formula

namespace Formula
variable {F}
def eval (xs : Assignment F) : Formula F → Prop
  | .truth => True
  | .sort k => QuotientPairQF.hiddenSort (CloneSAP.source B.source) (xs k) = ⟨i,(F.symbol k).val⟩
  | .pair k l test => ∃ x : Quotient (F.symbol k).val.val, ∃ y : Quotient (F.symbol l).val.val,
      QuotientPairQF.hiddenPoint (CloneSAP.source B.source) (F.symbol k).val x = xs k ∧
      QuotientPairQF.hiddenPoint (CloneSAP.source B.source) (F.symbol l).val y = xs l ∧ test.eval x y
  | .conj a b => a.eval xs ∧ b.eval xs

def conjoin : List (Formula F) → Formula F
  | [] => .truth
  | a :: as => .conj a (conjoin as)

theorem eval_conjoin (ps : List (Formula F)) (a : Assignment F) :
    (conjoin ps).eval a ↔ ∀ test ∈ ps, test.eval a := by
  induction ps with
  | nil => simp [conjoin,eval]
  | cons f fs ih => simp [conjoin,eval,ih]
end Formula

def coordinates : List F.Index := by
  classical
  letI : Fintype F.Index := Fintype.ofFinite _
  exact Finset.univ.toList

theorem mem_coordinates (a : F.Index) : a ∈ coordinates F := by
  classical
  simp [coordinates]

def typedAssignment (a : F.Tuple) : Assignment F :=
  fun k => QuotientPairQF.hiddenPoint (CloneSAP.source B.source) (F.symbol k).val (a k)

theorem pair_typed (k l : F.Index)
    (test : QuotientPairQF.Formula (CloneSAP.source B.source) (F.symbol k).val (F.symbol l).val)
    (a : F.Tuple) :
    (Formula.pair k l test).eval (typedAssignment F a) ↔ test.eval (a k) (a l) := by
  constructor
  · rintro ⟨x,y,hx,hy,h⟩
    have hx' := QuotientPairQF.hiddenPoint_injective (CloneSAP.source B.source) (F.symbol k).val hx
    have hy' := QuotientPairQF.hiddenPoint_injective (CloneSAP.source B.source) (F.symbol l).val hy
    simpa only [hx',hy'] using h
  · intro h
    exact ⟨a k,a l,rfl,rfl,h⟩

def domainFormula : Formula F :=
  Formula.conjoin ((coordinates F).map Formula.sort ++
    (coordinates F).flatMap (fun k => (coordinates F).map (fun l =>
      Formula.pair k l (QuotientPairQF.membershipFormula (CloneSAP.source B.source)
        (F.symbol k).val (F.symbol l).val (Sum.inr ⟨rfl⟩)))))

theorem domain_eval (a : Assignment F) :
    (domainFormula F).eval a ↔
      (∀ k, (Formula.sort k).eval a) ∧
      ∀ k l, (Formula.pair k l (QuotientPairQF.membershipFormula (CloneSAP.source B.source)
        (F.symbol k).val (F.symbol l).val (Sum.inr ⟨rfl⟩))).eval a := by
  rw [domainFormula,Formula.eval_conjoin]
  constructor
  · intro h
    constructor
    · intro k
      exact h _ (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨k,mem_coordinates F k,rfl⟩)))
    · intro k l
      exact h _ (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
        ⟨k,mem_coordinates F k,List.mem_map.mpr ⟨l,mem_coordinates F l,rfl⟩⟩)))
  · rintro ⟨hs,hp⟩ test ht
    rcases List.mem_append.mp ht with h | h
    · obtain ⟨k,_,rfl⟩ := List.mem_map.mp h
      exact hs k
    · obtain ⟨k,_,h⟩ := List.mem_flatMap.mp h
      obtain ⟨l,_,rfl⟩ := List.mem_map.mp h
      exact hp k l

theorem domain_typed (a : F.Tuple) :
    (domainFormula F).eval (typedAssignment F a) ↔ F.Compatible a := by
  rw [domain_eval]
  constructor
  · rintro ⟨_,h⟩ k l
    exact (QuotientPairQF.membershipFormula_eval (CloneSAP.source B.source)
      (CloneSAP.homogeneous B.source B.homogeneous) (F.symbol k).val (F.symbol l).val
      (Sum.inr ⟨rfl⟩) (a k) (a l)).mp ((pair_typed F k l _ a).mp (h k l))
  · intro h
    refine ⟨fun _ => rfl,?_⟩
    intro k l
    apply (pair_typed F k l _ a).mpr
    exact (QuotientPairQF.membershipFormula_eval (CloneSAP.source B.source)
      (CloneSAP.homogeneous B.source B.homogeneous) (F.symbol k).val (F.symbol l).val
      (Sum.inr ⟨rfl⟩) (a k) (a l)).mpr (h k l)

/-- The exact same finite QF domain for any chosen meet-K family, without
adjoining coordinates from the all-MI default or making a section choice. -/
theorem domain_unique_owner (ht : B.Terminal) (a : Assignment F) :
    (domainFormula F).eval a ↔ ∃! x : B.Point i, ∀ k,
      a k = QuotientPairQF.hiddenPoint (CloneSAP.source B.source) (F.symbol k).val (F.ownerTuple x k) := by
  constructor
  · intro ha
    have hs := ((domain_eval F a).mp ha).1
    have hex (k : F.Index) : ∃ q : Quotient (F.symbol k).val.val,
        QuotientPairQF.hiddenPoint (CloneSAP.source B.source) (F.symbol k).val q = a k :=
      QuotientPairQF.hiddenPoint_of_sort (CloneSAP.source B.source) (F.symbol k).val (a k) (hs k)
    choose q hq using hex
    have he : a = typedAssignment F q := funext (fun k => (hq k).symm)
    rw [he] at ha
    obtain ⟨x,hx,_⟩ := (F.tuple_domain ht q).mpr ((domain_typed F q).mp ha)
    have hout (k : F.Index) : a k = QuotientPairQF.hiddenPoint (CloneSAP.source B.source)
        (F.symbol k).val (F.ownerTuple x k) := by
      rw [he]
      exact congrArg (QuotientPairQF.hiddenPoint (CloneSAP.source B.source) (F.symbol k).val)
        (congrFun hx k).symm
    refine ⟨x,hout,?_⟩
    intro y hy
    apply F.ownerTuple_injective
    funext k
    exact QuotientPairQF.hiddenPoint_injective (CloneSAP.source B.source) (F.symbol k).val
      ((hy k).symm.trans (hout k))
  · rintro ⟨x,hx,_⟩
    have he : a = typedAssignment F (F.ownerTuple x) := funext hx
    rw [he]
    apply (domain_typed F _).mpr
    exact (F.tuple_domain ht _).mp ⟨x,rfl,fun y hy => F.ownerTuple_injective hy⟩

variable {j : B.Sorts} (G : SelectedMIFamily.{u,v,w,q} B j)

def readoutFormula (a : (CloneSAP.source B.source).Atom i j) :
    List ((k : F.Index) × (l : G.Index) ×
      QuotientPairQF.Formula (CloneSAP.source B.source) (F.symbol k).val (G.symbol l).val) :=
  (coordinates F).flatMap (fun k => (coordinates G).map (fun l =>
    ⟨k,l,QuotientPairQF.membershipFormula (CloneSAP.source B.source) (F.symbol k).val (G.symbol l).val a⟩))

def readoutEval (a : (CloneSAP.source B.source).Atom i j) (x : F.Tuple) (y : G.Tuple) : Prop :=
  ∀ test ∈ readoutFormula F G a, test.2.2.eval (x test.1) (y test.2.1)

theorem readout_eval (a : (CloneSAP.source B.source).Atom i j) (x : F.Tuple) (y : G.Tuple) :
    readoutEval F G a x y ↔ a ∈ pairSpectrum F G x y := by
  constructor
  · intro h k l
    have hm : (⟨k,l,QuotientPairQF.membershipFormula (CloneSAP.source B.source)
        (F.symbol k).val (G.symbol l).val a⟩) ∈ readoutFormula F G a :=
      List.mem_flatMap.mpr ⟨k,mem_coordinates F k,List.mem_map.mpr ⟨l,mem_coordinates G l,rfl⟩⟩
    exact (QuotientPairQF.membershipFormula_eval (CloneSAP.source B.source)
      (CloneSAP.homogeneous B.source B.homogeneous) (F.symbol k).val (G.symbol l).val
      a (x k) (y l)).mp (h _ hm)
  · intro h test ht
    obtain ⟨k,_,ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨l,_,rfl⟩ := List.mem_map.mp ht
    exact (QuotientPairQF.membershipFormula_eval (CloneSAP.source B.source)
      (CloneSAP.homogeneous B.source B.homogeneous) (F.symbol k).val (G.symbol l).val
      a (x k) (y l)).mpr (h k l)

theorem original_colour_readout (ht : B.Terminal)
    (x : B.Point i) (y : B.Point j) (a : B.source.Atom i j) :
    readoutEval F G (Sum.inl a) (F.ownerTuple x) (G.ownerTuple y) ↔ B.source.atomRel a x y :=
  (readout_eval F G _ _ _).trans (F.original_colour_iff G ht x y a)

section FiniteHidden
variable {V : Type z} (D : OwnerStage.FiniteHidden.Object B V)

def finiteEval (F : SelectedMIFamily.{u,v,w,p} B i)
    (D : OwnerStage.FiniteHidden.Object B V) (xs : F.Index → V) : Formula F → Prop
  | .truth => True
  | .sort k => D.sort (xs k) = ⟨i,(F.symbol k).val⟩
  | .pair k l test => D.sort (xs k) = ⟨i,(F.symbol k).val⟩ ∧
      D.sort (xs l) = ⟨i,(F.symbol l).val⟩ ∧ D.pairEval (xs k) (xs l) test
  | .conj a b => finiteEval F D xs a ∧ finiteEval F D xs b

abbrev VisibleTuple := {xs : F.Index → V // finiteEval F D xs (domainFormula F)}

instance visibleTuple_finite : Finite (VisibleTuple F D) := by
  let := D.finite
  infer_instance

variable (e : OwnerStage.FiniteHidden.Realization D)

theorem finite_transport (test : Formula F) (xs : F.Index → V) :
    test.eval (e.point ∘ xs) ↔ finiteEval F D xs test := by
  induction test with
  | truth => exact Iff.rfl
  | sort k =>
      change QuotientPairQF.hiddenSort (CloneSAP.source B.source) (e.point (xs k)) = _ ↔ _
      rw [e.sort_eq]
      rfl
  | pair k l test =>
      constructor
      · rintro ⟨x,y,hx,hy,h⟩
        exact ⟨(e.sort_eq (xs k)).symm.trans
            (congrArg (QuotientPairQF.hiddenSort (CloneSAP.source B.source)) hx).symm,
          (e.sort_eq (xs l)).symm.trans
            (congrArg (QuotientPairQF.hiddenSort (CloneSAP.source B.source)) hy).symm,
          (e.pair_transport test (xs k) (xs l) x y hx hy).mp h⟩
      · rintro ⟨hsx,hsy,h⟩
        obtain ⟨x,hx⟩ := QuotientPairQF.hiddenPoint_of_sort (CloneSAP.source B.source)
          (F.symbol k).val (e.point (xs k)) ((e.sort_eq (xs k)).trans hsx)
        obtain ⟨y,hy⟩ := QuotientPairQF.hiddenPoint_of_sort (CloneSAP.source B.source)
          (F.symbol l).val (e.point (xs l)) ((e.sort_eq (xs l)).trans hsy)
        exact ⟨x,y,hx,hy,(e.pair_transport test (xs k) (xs l) x y hx hy).mpr h⟩
  | conj a b ih ih' => exact and_congr ih ih'

theorem finite_domain_independent (f : OwnerStage.FiniteHidden.Realization D)
    (xs : F.Index → V) :
    (domainFormula F).eval (e.point ∘ xs) ↔ (domainFormula F).eval (f.point ∘ xs) :=
  (finite_transport F D e _ xs).trans (finite_transport F D f _ xs).symm

theorem owner_exists (ht : B.Terminal) (xs : VisibleTuple F D) :
    ∃! x : B.Point i, ∀ k,
      e.point (xs.val k) = QuotientPairQF.hiddenPoint (CloneSAP.source B.source)
        (F.symbol k).val (F.ownerTuple x k) :=
  (domain_unique_owner F ht (e.point ∘ xs.val)).mp
    ((finite_transport F D e _ xs.val).mpr xs.property)

def owner (ht : B.Terminal) (xs : VisibleTuple F D) : B.Point i :=
  (owner_exists F D e ht xs).choose

theorem owner_spec (ht : B.Terminal) (xs : VisibleTuple F D) (k : F.Index) :
    e.point (xs.val k) = QuotientPairQF.hiddenPoint (CloneSAP.source B.source)
      (F.symbol k).val (F.ownerTuple (owner F D e ht xs) k) :=
  (owner_exists F D e ht xs).choose_spec.1 k

theorem owner_injective (ht : B.Terminal) : Function.Injective (owner F D e ht) := by
  intro xs ys h
  apply Subtype.ext
  funext k
  apply e.point.injective
  exact (owner_spec F D e ht xs k).trans
    ((congrArg (fun x => QuotientPairQF.hiddenPoint (CloneSAP.source B.source) (F.symbol k).val
      (F.ownerTuple x k)) h).trans (owner_spec F D e ht ys k).symm)

def finiteReadout (a : B.source.Atom i j) (xs : VisibleTuple F D) (ys : VisibleTuple G D) : Prop :=
  ∀ test ∈ readoutFormula F G (Sum.inl a), D.pairEval (xs.val test.1) (ys.val test.2.1) test.2.2

theorem finite_colour_readout (ht : B.Terminal) (a : B.source.Atom i j)
    (xs : VisibleTuple F D) (ys : VisibleTuple G D) :
    finiteReadout F G D a xs ys ↔
      B.source.atomRel a (owner F D e ht xs) (owner G D e ht ys) := by
  have he : finiteReadout F G D a xs ys ↔
      readoutEval F G (Sum.inl a) (F.ownerTuple (owner F D e ht xs))
        (G.ownerTuple (owner G D e ht ys)) := by
    constructor
    · intro h test hmem
      exact (e.pair_transport test.2.2 (xs.val test.1) (ys.val test.2.1) _ _
        (owner_spec F D e ht xs test.1).symm (owner_spec G D e ht ys test.2.1).symm).mpr (h test hmem)
    · intro h test hmem
      exact (e.pair_transport test.2.2 (xs.val test.1) (ys.val test.2.1) _ _
        (owner_spec F D e ht xs test.1).symm (owner_spec G D e ht ys test.2.1).symm).mp (h test hmem)
  exact he.trans (original_colour_readout F G ht _ _ a)

theorem finite_colour_independent (f : OwnerStage.FiniteHidden.Realization D) (ht : B.Terminal)
    (xs : VisibleTuple F D) (ys : VisibleTuple G D) :
    B.source.colour (owner F D e ht xs) (owner G D e ht ys) =
      B.source.colour (owner F D f ht xs) (owner G D f ht ys) := by
  apply Option.ext
  intro a
  exact (finite_colour_readout F G D e ht a xs ys).symm.trans
    (finite_colour_readout F G D f ht a xs ys)

end FiniteHidden

section WholeFiniteReconstruction
variable (families : ∀ i : B.Sorts, SelectedMIFamily.{u,v,w,p} B i)
variable {V : Type z} (D : OwnerStage.FiniteHidden.Object B V)

abbrev VisiblePoint := (i : B.Sorts) × VisibleTuple (families i) D

instance visiblePoint_finite : Finite (VisiblePoint families D) := by
  let := B.source.finiteSort
  infer_instance

variable (e : OwnerStage.FiniteHidden.Realization D)

def visiblePoint (ht : B.Terminal) (x : VisiblePoint families D) : Sigma B.Point :=
  ⟨x.1,owner (families x.1) D e ht x.2⟩

theorem visiblePoint_injective (ht : B.Terminal) : Function.Injective (visiblePoint families D e ht) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ h
  have hij : i = j := congrArg Sigma.fst h
  subst j
  have hxy := owner_injective (families i) D e ht (eq_of_heq (Sigma.mk.inj h).2)
  cases hxy
  rfl

def visibleTable (ht : B.Terminal) : Age.Table B.source (VisiblePoint families D) :=
  Age.table B.source (visiblePoint families D e ht) (fun _ => 0)

theorem visibleTable_realized (ht : B.Terminal) :
    Age.Realized B.source (Age.zeroMask B.source) (visibleTable families D e ht) :=
  ⟨visiblePoint families D e ht,(fun _ => 0),visiblePoint_injective families D e ht,
    ⟨fun _ => rfl,fun _ _ => ⟨rfl,rfl⟩⟩,rfl⟩

theorem visibleTable_independent (f : OwnerStage.FiniteHidden.Realization D) (ht : B.Terminal) :
    visibleTable families D e ht = visibleTable families D f ht := by
  apply congrArg₂ OwnerTransversal.CountableColour.Table.mk
  · rfl
  · funext x y
    rcases x with ⟨i,x⟩
    rcases y with ⟨j,y⟩
    exact congrArg (fun c => Age.colourEquiv B.source (⟨i,j,c⟩ : Age.Colour B.source))
      (finite_colour_independent (families i) (families j) D e f ht x y)

def visibleChart (ht : B.Terminal) : Age.Chart B.source (Age.zeroMask B.source) := by
  letI : Fintype (VisiblePoint families D) := Fintype.ofFinite _
  let enum := (Fintype.equivFin (VisiblePoint families D)).symm
  exact Age.chartOf B.source (Age.reindex B.source (visibleTable families D e ht) enum)
    (Age.realized_reindex B.source (visibleTable_realized families D e ht) enum.toEmbedding)

private theorem chart_ext {C K : Age.Chart B.source (Age.zeroMask B.source)}
    (hs : C.size = K.size) (ht : HEq C.table K.table) : C = K := by
  cases C
  cases K
  cases hs
  cases eq_of_heq ht
  rfl

theorem visibleChart_independent (f : OwnerStage.FiniteHidden.Realization D) (ht : B.Terminal) :
    visibleChart families D e ht = visibleChart families D f ht := by
  apply chart_ext (C := visibleChart families D e ht) (K := visibleChart families D f ht) rfl
  dsimp only [visibleChart,Age.chartOf]
  rw [visibleTable_independent families D e f ht]

/-- The full finite reconstruction consumer for the freely chosen family
at each source sort. ONE actual hidden realization works for all tuples;
the resulting complete owner table and chart do not depend on that choice. -/
theorem finite_hidden_reconstruction (ht : B.Terminal)
    (member : OwnerStage.FiniteHidden.Member D) :
    ∃ e : OwnerStage.FiniteHidden.Realization D,
      Function.Injective (visiblePoint families D e ht) ∧
      Age.Realized B.source (Age.zeroMask B.source) (visibleTable families D e ht) ∧
      ∀ f : OwnerStage.FiniteHidden.Realization D,
        visibleTable families D e ht = visibleTable families D f ht ∧
        visibleChart families D e ht = visibleChart families D f ht := by
  obtain ⟨e⟩ := member
  exact ⟨e,visiblePoint_injective families D e ht,visibleTable_realized families D e ht,
    fun f => ⟨visibleTable_independent families D e f ht,visibleChart_independent families D e f ht⟩⟩

end WholeFiniteReconstruction

end QF

/-- Source-facing D05/C25 generality: the fixed coordinate family at each
sort may be ANY finite distinct proper FULL MI family with meet K. All
unary-tagged QF domains, old-colour readouts and whole finite reconstruction
use precisely those chosen coordinates; the all-MI default is unnecessary. -/
theorem ramsey_selected_family_geometry
    (families : ∀ i : B.Sorts, SelectedMIFamily.{u,v,w,p} B i) (ht : B.Terminal) :
    (∀ i, Nonempty (families i).Index ∧
      Function.Injective (families i).ownerTuple) ∧
    (∀ i (xs : QF.Assignment (families i)),
      (QF.domainFormula (families i)).eval xs ↔ ∃! x : B.Point i, ∀ k,
        xs k = QuotientPairQF.hiddenPoint (CloneSAP.source B.source)
          ((families i).symbol k).val ((families i).ownerTuple x k)) ∧
    (∀ {i j : B.Sorts} (x : B.Point i) (y : B.Point j) (a : B.source.Atom i j),
      QF.readoutEval (families i) (families j) (Sum.inl a)
        ((families i).ownerTuple x) ((families j).ownerTuple y) ↔ B.source.atomRel a x y) ∧
    (∀ {V : Type z} (D : OwnerStage.FiniteHidden.Object B V), OwnerStage.FiniteHidden.Member D →
      ∃ e : OwnerStage.FiniteHidden.Realization D,
        Function.Injective (QF.visiblePoint families D e ht) ∧
        Age.Realized B.source (Age.zeroMask B.source) (QF.visibleTable families D e ht) ∧
        ∀ f : OwnerStage.FiniteHidden.Realization D,
          QF.visibleTable families D e ht = QF.visibleTable families D f ht ∧
          QF.visibleChart families D e ht = QF.visibleChart families D f ht) := by
  refine ⟨fun i => ⟨(families i).nonemptyIndex,(families i).ownerTuple_injective⟩,
    fun i xs => QF.domain_unique_owner (families i) ht xs,
    fun x y a => QF.original_colour_readout _ _ ht x y a,?_⟩
  intro V D member
  exact QF.finite_hidden_reconstruction families D ht member

end
end CCO.CloneTupleGeometry.OwnerStage.SelectedMIFamily
