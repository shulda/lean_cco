import CCO.CloneTupleGeometry.QuantifierFreeSpectrum
import CCO.CloneTupleGeometry.TerminalSingletonRecovery

/-! A literal finite quantifier-free domain formula on the actual hidden
coordinate vertices. Unary atoms enforce the hidden sort tags; its binary
tests are the finite B049 name disjunctions, with real hidden equality
handled separately. An orphan tuple satisfying this formula represents one
unique owner, even if that owner is outside the displayed hidden support. -/

universe u v w
namespace CCO.CloneTupleGeometry.OwnerStage
open ParityHasse.Original
noncomputable section
variable (B : OwnerStage.{u,v,w}) (i : B.Sorts)

namespace TupleQF

abbrev HiddenPoint := QuotientPairQF.HiddenPoint (CloneSAP.source B.source)
abbrev Assignment := FullCloneProperMI B.source i → HiddenPoint B

/-- Boolean syntax over coordinate slots. A pair instruction contains
only the finite typed equality/cylinder syntax of QuantifierFreeSpectrum. -/
inductive Formula where
  | truth : Formula
  | sort (J : FullCloneProperMI B.source i) : Formula
  | pair (J L : FullCloneProperMI B.source i)
      (p : QuotientPairQF.Formula (CloneSAP.source B.source) J.val L.val) : Formula
  | conj (p q : Formula) : Formula

namespace Formula
variable {B i}

def eval (a : Assignment B i) : Formula B i → Prop
  | .truth => True
  | .sort J => QuotientPairQF.hiddenSort (CloneSAP.source B.source) (a J) = ⟨i,J.val⟩
  | .pair J L p => ∃ q : Quotient J.val.val, ∃ r : Quotient L.val.val,
      QuotientPairQF.hiddenPoint (CloneSAP.source B.source) J.val q = a J ∧
      QuotientPairQF.hiddenPoint (CloneSAP.source B.source) L.val r = a L ∧ p.eval q r
  | .conj p q => p.eval a ∧ q.eval a

def conjoin : List (Formula B i) → Formula B i
  | [] => .truth
  | p :: ps => .conj p (conjoin ps)

theorem eval_conjoin (ps : List (Formula B i)) (a : Assignment B i) :
    (conjoin ps).eval a ↔ ∀ p ∈ ps, p.eval a := by
  induction ps with
  | nil => simp [conjoin,eval]
  | cons p ps ih => simp [conjoin,eval,ih]
end Formula

def coordinates : List (FullCloneProperMI B.source i) := by
  classical
  letI : Fintype (FullCloneProperMI B.source i) := Fintype.ofFinite _
  exact Finset.univ.toList

theorem mem_coordinates (J : FullCloneProperMI B.source i) : J ∈ coordinates B i := by
  classical
  simp [coordinates]

def typedAssignment (q : FullCloneMITuple B.source i) : Assignment B i :=
  fun J => QuotientPairQF.hiddenPoint (CloneSAP.source B.source) J.val (q J)

theorem eval_pair_typed (J L : FullCloneProperMI B.source i)
    (p : QuotientPairQF.Formula (CloneSAP.source B.source) J.val L.val)
    (q : FullCloneMITuple B.source i) :
    (Formula.pair J L p).eval (typedAssignment B i q) ↔ p.eval (q J) (q L) := by
  constructor
  · rintro ⟨x,y,hx,hy,hp⟩
    have hxq := QuotientPairQF.hiddenPoint_injective (CloneSAP.source B.source) J.val hx
    have hyq := QuotientPairQF.hiddenPoint_injective (CloneSAP.source B.source) L.val hy
    simpa only [hxq,hyq] using hp
  · intro hp
    exact ⟨q J,q L,rfl,rfl,hp⟩

/-- The fixed finite conjunction includes unary sort tags and all clone
membership tests. Diagonal/reversed tests may be redundant but make the
one-coordinate case literal and preserve every repeated-coordinate case. -/
def domainFormula : Formula B i :=
  Formula.conjoin ((coordinates B i).map Formula.sort ++
    (coordinates B i).flatMap (fun J => (coordinates B i).map (fun L =>
      Formula.pair J L (QuotientPairQF.membershipFormula
        (CloneSAP.source B.source) J.val L.val (Sum.inr ⟨rfl⟩)))))

theorem domainFormula_eval (a : Assignment B i) :
    (domainFormula B i).eval a ↔
      (∀ J, (Formula.sort J).eval a) ∧
      ∀ J L, (Formula.pair J L (QuotientPairQF.membershipFormula
        (CloneSAP.source B.source) J.val L.val (Sum.inr ⟨rfl⟩))).eval a := by
  rw [domainFormula,Formula.eval_conjoin]
  constructor
  · intro ha
    constructor
    · intro J
      exact ha _ (List.mem_append.mpr (Or.inl
        (List.mem_map.mpr ⟨J,mem_coordinates B i J,rfl⟩)))
    · intro J L
      exact ha _ (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
        ⟨J,mem_coordinates B i J,List.mem_map.mpr ⟨L,mem_coordinates B i L,rfl⟩⟩)))
  · rintro ⟨hs,hp⟩ f hf
    rcases List.mem_append.mp hf with hf | hf
    · obtain ⟨J,_,rfl⟩ := List.mem_map.mp hf
      exact hs J
    · obtain ⟨J,_,hf⟩ := List.mem_flatMap.mp hf
      obtain ⟨L,_,rfl⟩ := List.mem_map.mp hf
      exact hp J L

theorem domainFormula_typed (q : FullCloneMITuple B.source i) :
    (domainFormula B i).eval (typedAssignment B i q) ↔ B.TupleCompatible i q := by
  rw [domainFormula_eval]
  constructor
  · rintro ⟨_,h⟩ J L
    have hp := (eval_pair_typed B i J L _ q).mp (h J L)
    exact (QuotientPairQF.membershipFormula_eval (CloneSAP.source B.source)
      (CloneSAP.homogeneous B.source B.homogeneous) J.val L.val (Sum.inr ⟨rfl⟩) (q J) (q L)).mp hp
  · intro h
    refine ⟨fun _ => rfl,?_⟩
    intro J L
    apply (eval_pair_typed B i J L _ q).mpr
    exact (QuotientPairQF.membershipFormula_eval (CloneSAP.source B.source)
      (CloneSAP.homogeneous B.source B.homogeneous) J.val L.val (Sum.inr ⟨rfl⟩) (q J) (q L)).mpr (h J L)

/-- Actual tagged quantifier-free tuple domain, including arbitrary orphan
coordinate assignments in the actual hidden data. No owner vertex or cell
is required inside the displayed hidden object. -/
theorem domainFormula_unique_owner (ht : B.Terminal) (a : Assignment B i) :
    (domainFormula B i).eval a ↔
      ∃! x : B.Point i, ∀ J,
        a J = QuotientPairQF.hiddenPoint (CloneSAP.source B.source) J.val
          (originalOwnerMITuple B.source i x J) := by
  constructor
  · intro ha
    have hs := ((domainFormula_eval B i a).mp ha).1
    have hex (J : FullCloneProperMI B.source i) :
        ∃ q : Quotient J.val.val,
          QuotientPairQF.hiddenPoint (CloneSAP.source B.source) J.val q = a J :=
      QuotientPairQF.hiddenPoint_of_sort (CloneSAP.source B.source) J.val (a J) (hs J)
    choose q hq using hex
    have he : a = typedAssignment B i q := funext (fun J => (hq J).symm)
    rw [he] at ha
    obtain ⟨x,hx,_⟩ := (B.terminal_tuple_domain i ht q).mpr ((domainFormula_typed B i q).mp ha)
    have hout (J : FullCloneProperMI B.source i) :
        a J = QuotientPairQF.hiddenPoint (CloneSAP.source B.source) J.val
          (originalOwnerMITuple B.source i x J) := by
      rw [he]
      exact congrArg (QuotientPairQF.hiddenPoint (CloneSAP.source B.source) J.val)
        (congrFun hx J).symm
    refine ⟨x,hout,?_⟩
    intro y hy
    apply originalOwnerMITuple_injective B.source i
    funext J
    exact QuotientPairQF.hiddenPoint_injective (CloneSAP.source B.source) J.val
      ((hy J).symm.trans (hout J))
  · rintro ⟨x,hx,_⟩
    have he : a = typedAssignment B i (originalOwnerMITuple B.source i x) := funext hx
    rw [he]
    exact (domainFormula_typed B i _).mpr (B.owner_tuple_compatible i x)

end TupleQF

/-- A finite conjunction of typed equality/cylinder formulas on all mixed
coordinate pairs. This is the quantifier-free fine-colour membership
formula, independent of whether two hidden coordinates happen to coincide. -/
def spectrumReadoutFormula {j : B.Sorts} (a : (CloneSAP.source B.source).Atom i j) :
    List ((J : FullCloneProperMI B.source i) × (L : FullCloneProperMI B.source j) ×
      QuotientPairQF.Formula (CloneSAP.source B.source) J.val L.val) :=
  (TupleQF.coordinates B i).flatMap (fun J => (TupleQF.coordinates B j).map (fun L =>
    ⟨J,L,QuotientPairQF.membershipFormula (CloneSAP.source B.source) J.val L.val a⟩))

def spectrumReadoutEval {j : B.Sorts} (a : (CloneSAP.source B.source).Atom i j)
    (q : FullCloneMITuple B.source i) (r : FullCloneMITuple B.source j) : Prop :=
  ∀ f ∈ spectrumReadoutFormula B i a, f.2.2.eval (q f.1) (r f.2.1)

theorem spectrumReadoutFormula_eval {j : B.Sorts} (a : (CloneSAP.source B.source).Atom i j)
    (q : FullCloneMITuple B.source i) (r : FullCloneMITuple B.source j) :
    B.spectrumReadoutEval i a q r ↔ a ∈ B.tuplePairSpectrum q r := by
  constructor
  · intro h J L
    have hm : (⟨J,L,QuotientPairQF.membershipFormula
        (CloneSAP.source B.source) J.val L.val a⟩) ∈ spectrumReadoutFormula B i a :=
      List.mem_flatMap.mpr ⟨J,TupleQF.mem_coordinates B i J,
        List.mem_map.mpr ⟨L,TupleQF.mem_coordinates B j L,rfl⟩⟩
    exact (QuotientPairQF.membershipFormula_eval (CloneSAP.source B.source)
      (CloneSAP.homogeneous B.source B.homogeneous) J.val L.val a (q J) (r L)).mp (h _ hm)
  · intro h f hf
    obtain ⟨J,_,hf⟩ := List.mem_flatMap.mp hf
    obtain ⟨L,_,rfl⟩ := List.mem_map.mp hf
    exact (QuotientPairQF.membershipFormula_eval (CloneSAP.source B.source)
      (CloneSAP.homogeneous B.source B.homogeneous) J.val L.val a (q J) (r L)).mpr (h J L)

set_option backward.isDefEq.respectTransparency.types false in
/-- Every original typed fine colour is defined by the actual finite
quantifier-free mixed-spectrum formula on owner tuples. The equality
case gives the clone marker and therefore satisfies no old diversity
formula, even when some or all hidden coordinates coincide. -/
theorem original_colour_readout (ht : B.Terminal) {j : B.Sorts}
    (q : B.Point i) (r : B.Point j) (a : B.source.Atom i j) :
    B.spectrumReadoutEval i (Sum.inl a) (originalOwnerMITuple B.source i q)
      (originalOwnerMITuple B.source j r) ↔ B.source.atomRel a q r := by
  rw [spectrumReadoutFormula_eval]
  constructor
  · intro ha
    cases hc : B.source.colour q r with
    | none =>
        have he := (B.source.colour_none_iff q r).mp hc
        have hij : i = j := congrArg Sigma.fst he
        subst j
        have hqr : q = r := eq_of_heq (Sigma.mk.inj he).2
        subst r
        rw [B.terminal_equal_owner_singleton ht q] at ha
        cases Set.mem_singleton_iff.mp ha
    | some b =>
        rw [B.terminal_original_pair_singleton ht q r b hc] at ha
        have hab : a = b := Sum.inl.inj (Set.mem_singleton_iff.mp ha)
        subst a
        exact hc
  · intro h
    rw [B.terminal_original_pair_singleton ht q r a h]
    rfl

end
end CCO.CloneTupleGeometry.OwnerStage
