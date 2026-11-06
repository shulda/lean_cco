import CCO.CloneTupleGeometry.QuantifierFreeDomain
import CCO.APCharacter.Age.Category

/-! Faithful reconstruction of ONE finite completed hidden object.
Membership means one induced realization of its WHOLE vertex set in the
actual typed quotient data. Valid tuples need no additional cell vertex.
All of them are reconstructed together; unary tags, equality and complete
named cylinders make the resulting finite visible structure independent
of the chosen whole realization. No hidden SAP or CCO is asserted. -/

set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace CCO.CloneTupleGeometry.OwnerStage
open ParityHasse.Original APCharacter
noncomputable section
variable (B : OwnerStage.{u,v,w})

namespace FiniteHidden
abbrev HiddenSort := (i : B.Sorts) × ColourEq (CloneSAP.source B.source) i
abbrev HiddenPoint := QuotientPairQF.HiddenPoint (CloneSAP.source B.source)

/-- All symbol families used here are finite because the FULL invariant
kernel lattices and the actual complete cylinder-name palettes are finite. -/
abbrev BinarySymbol := (i : B.Sorts) × (j : B.Sorts) ×
  (J : ColourEq (CloneSAP.source B.source) i) ×
  (K : ColourEq (CloneSAP.source B.source) j) ×
  QuotientPairQF.Name (CloneSAP.source B.source) J K

instance binarySymbol_finite : Finite (BinarySymbol B) := by
  let := B.source.finiteSort
  infer_instance

/-- The actual interpretation of one B049 binary symbol on tagged hidden
vertices. Its predicate omits only equality in the same hidden sort. -/
def actualNamed {i j : B.Sorts}
    {J : ColourEq (CloneSAP.source B.source) i}
    {K : ColourEq (CloneSAP.source B.source) j}
    (P : QuotientPairQF.Name (CloneSAP.source B.source) J K)
    (x y : HiddenPoint B) : Prop :=
  ∃ q : Quotient J.val, ∃ r : Quotient K.val,
    QuotientPairQF.hiddenPoint (CloneSAP.source B.source) J q = x ∧
    QuotientPairQF.hiddenPoint (CloneSAP.source B.source) K r = y ∧
    QuotientPairQF.NamedRelation (CloneSAP.source B.source) P q r

theorem actualNamed_typed {i j : B.Sorts}
    {J : ColourEq (CloneSAP.source B.source) i}
    {K : ColourEq (CloneSAP.source B.source) j}
    (P : QuotientPairQF.Name (CloneSAP.source B.source) J K)
    (q : Quotient J.val) (r : Quotient K.val) :
    actualNamed B P (QuotientPairQF.hiddenPoint (CloneSAP.source B.source) J q)
      (QuotientPairQF.hiddenPoint (CloneSAP.source B.source) K r) ↔
      QuotientPairQF.NamedRelation (CloneSAP.source B.source) P q r := by
  constructor
  · rintro ⟨q',r',hq,hr,h⟩
    have hq' := QuotientPairQF.hiddenPoint_injective (CloneSAP.source B.source) J hq
    have hr' := QuotientPairQF.hiddenPoint_injective (CloneSAP.source B.source) K hr
    simpa only [hq',hr'] using h
  · intro h
    exact ⟨q,r,rfl,rfl,h⟩

/-- Finite relational shadow of a pure-imaginary hidden object. Proper MI
sort tags are explicit; the complete actual cylinder names are retained. -/
structure Object (V : Type z) where
  finite : Finite V
  sort : V → HiddenSort B
  proper : ∀ x, ∃ J : FullCloneProperMI B.source (sort x).1, J.val = (sort x).2
  binary : ∀ {i j : B.Sorts} (J : ColourEq (CloneSAP.source B.source) i)
    (K : ColourEq (CloneSAP.source B.source) j),
    QuotientPairQF.Name (CloneSAP.source B.source) J K → V → V → Prop

variable {B} {V : Type z}

/-- ONE whole induced embedding: all vertices, unary sort tags, equality
and every actual named cylinder predicate are preserved and reflected. -/
structure Realization (D : Object B V) where
  point : V ↪ HiddenPoint B
  sort_eq : ∀ x, QuotientPairQF.hiddenSort (CloneSAP.source B.source) (point x) = D.sort x
  named_iff : ∀ {i j : B.Sorts} (J : ColourEq (CloneSAP.source B.source) i)
    (K : ColourEq (CloneSAP.source B.source) j)
    (P : QuotientPairQF.Name (CloneSAP.source B.source) J K) (x y : V),
    actualNamed B P (point x) (point y) ↔ D.binary J K P x y

/-- Completed-age membership is actual simultaneous realization, rather
than independent witnesses for the different vertex pairs. -/
def Member (D : Object B V) : Prop := Nonempty (Realization D)

namespace Object
variable (D : Object B V)

def pairEval (D : Object B V) {i j : B.Sorts} {J : ColourEq (CloneSAP.source B.source) i}
    {K : ColourEq (CloneSAP.source B.source) j} (x y : V) :
    QuotientPairQF.Formula (CloneSAP.source B.source) J K → Prop
  | .falsum => False
  | .truth => True
  | .equal => x = y
  | .named P => D.binary J K P x y
  | .neg p => ¬pairEval D x y p
  | .conj p q => pairEval D x y p ∧ pairEval D x y q
  | .disj p q => pairEval D x y p ∨ pairEval D x y q

def tupleEval (D : Object B V) {i : B.Sorts} (a : FullCloneProperMI B.source i → V) : TupleQF.Formula B i → Prop
  | .truth => True
  | .sort J => D.sort (a J) = ⟨i,J.val⟩
  | .pair J L p => D.sort (a J) = ⟨i,J.val⟩ ∧ D.sort (a L) = ⟨i,L.val⟩ ∧
      D.pairEval (a J) (a L) p
  | .conj p q => tupleEval D a p ∧ tupleEval D a q

abbrev VisibleTuple (i : B.Sorts) :=
  {a : FullCloneProperMI B.source i → V // D.tupleEval a (TupleQF.domainFormula B i)}

instance visibleTuple_finite (i : B.Sorts) : Finite (D.VisibleTuple i) := by
  let := D.finite
  infer_instance

abbrev VisiblePoint := (i : B.Sorts) × D.VisibleTuple i

instance visiblePoint_finite : Finite D.VisiblePoint := by
  let := B.source.finiteSort
  infer_instance

/-- The same finite Boolean readout syntax, evaluated in the displayed
finite hidden object rather than with a new pairwise realization choice. -/
def colourReadout {i j : B.Sorts} (a : B.source.Atom i j)
    (q : D.VisibleTuple i) (r : D.VisibleTuple j) : Prop :=
  ∀ f ∈ spectrumReadoutFormula B i (Sum.inl a), D.pairEval (q.val f.1) (r.val f.2.1) f.2.2

end Object

namespace Realization
variable {D : Object B V} (e : Realization D)

/-- Only atomic preservation/reflection and literal equality injectivity
are used to transport the finite Boolean spectrum formulas. -/
theorem pair_transport {i j : B.Sorts}
    {J : ColourEq (CloneSAP.source B.source) i}
    {K : ColourEq (CloneSAP.source B.source) j}
    (p : QuotientPairQF.Formula (CloneSAP.source B.source) J K)
    (x y : V) (q : Quotient J.val) (r : Quotient K.val)
    (hq : QuotientPairQF.hiddenPoint (CloneSAP.source B.source) J q = e.point x)
    (hr : QuotientPairQF.hiddenPoint (CloneSAP.source B.source) K r = e.point y) :
    p.eval q r ↔ D.pairEval x y p := by
  induction p with
  | falsum => exact Iff.rfl
  | truth => exact Iff.rfl
  | equal =>
      change (QuotientPairQF.hiddenPoint (CloneSAP.source B.source) J q =
        QuotientPairQF.hiddenPoint (CloneSAP.source B.source) K r) ↔ x = y
      rw [hq,hr]
      exact ⟨fun h => e.point.injective h,fun h => congrArg e.point h⟩
  | named P =>
      have he := e.named_iff J K P x y
      rw [← hq,← hr,actualNamed_typed] at he
      exact he
  | neg p ih => exact not_congr ih
  | conj p p' ih ih' => exact and_congr ih ih'
  | disj p p' ih ih' => exact or_congr ih ih'

theorem tuple_transport {i : B.Sorts} (p : TupleQF.Formula B i)
    (a : FullCloneProperMI B.source i → V) :
    p.eval (e.point ∘ a) ↔ D.tupleEval a p := by
  induction p with
  | truth => exact Iff.rfl
  | sort J =>
      change QuotientPairQF.hiddenSort (CloneSAP.source B.source) (e.point (a J)) = ⟨i,J.val⟩ ↔ _
      rw [e.sort_eq]
      rfl
  | pair J L p =>
      constructor
      · rintro ⟨q,r,hq,hr,hp⟩
        have hsJ : D.sort (a J) = ⟨i,J.val⟩ :=
          (e.sort_eq (a J)).symm.trans
            (congrArg (QuotientPairQF.hiddenSort (CloneSAP.source B.source)) hq).symm
        have hsL : D.sort (a L) = ⟨i,L.val⟩ :=
          (e.sort_eq (a L)).symm.trans
            (congrArg (QuotientPairQF.hiddenSort (CloneSAP.source B.source)) hr).symm
        exact ⟨hsJ,hsL,(e.pair_transport p (a J) (a L) q r hq hr).mp hp⟩
      · rintro ⟨hsJ,hsL,hp⟩
        obtain ⟨q,hq⟩ := QuotientPairQF.hiddenPoint_of_sort (CloneSAP.source B.source)
          J.val (e.point (a J)) ((e.sort_eq (a J)).trans hsJ)
        obtain ⟨r,hr⟩ := QuotientPairQF.hiddenPoint_of_sort (CloneSAP.source B.source)
          L.val (e.point (a L)) ((e.sort_eq (a L)).trans hsL)
        exact ⟨q,r,hq,hr,(e.pair_transport p (a J) (a L) q r hq hr).mpr hp⟩
  | conj p q ih ih' => exact and_congr ih ih'

/-- Two entire induced realizations agree on domain validity, even for
orphan tuples containing no displayed original owner vertex. -/
theorem domain_independent (f : Realization D) {i : B.Sorts}
    (a : FullCloneProperMI B.source i → V) :
    (TupleQF.domainFormula B i).eval (e.point ∘ a) ↔
      (TupleQF.domainFormula B i).eval (f.point ∘ a) :=
  (e.tuple_transport _ a).trans (f.tuple_transport _ a).symm

theorem owner_exists (ht : B.Terminal) {i : B.Sorts} (q : D.VisibleTuple i) :
    ∃! x : B.Point i, ∀ J,
      e.point (q.val J) = QuotientPairQF.hiddenPoint (CloneSAP.source B.source) J.val
        (originalOwnerMITuple B.source i x J) :=
  (TupleQF.domainFormula_unique_owner B i ht (e.point ∘ q.val)).mp
    ((e.tuple_transport _ q.val).mpr q.property)

def owner (ht : B.Terminal) {i : B.Sorts} (q : D.VisibleTuple i) : B.Point i :=
  (e.owner_exists ht q).choose

theorem owner_spec (ht : B.Terminal) {i : B.Sorts} (q : D.VisibleTuple i)
    (J : FullCloneProperMI B.source i) :
    e.point (q.val J) = QuotientPairQF.hiddenPoint (CloneSAP.source B.source) J.val
      (originalOwnerMITuple B.source i (e.owner ht q) J) :=
  (e.owner_exists ht q).choose_spec.1 J

/-- All valid tuples reconstruct simultaneously and faithfully. Equal
owners force equality of every displayed coordinate through the SAME e. -/
theorem owner_injective (ht : B.Terminal) (i : B.Sorts) :
    Function.Injective (e.owner ht (i := i)) := by
  intro q r h
  apply Subtype.ext
  funext J
  apply e.point.injective
  exact (e.owner_spec ht q J).trans
    ((congrArg (fun x => QuotientPairQF.hiddenPoint (CloneSAP.source B.source) J.val
      (originalOwnerMITuple B.source i x J)) h).trans (e.owner_spec ht r J).symm)

def visiblePoint (ht : B.Terminal) (q : D.VisiblePoint) : Sigma B.Point :=
  ⟨q.1,e.owner ht q.2⟩

theorem visiblePoint_injective (ht : B.Terminal) : Function.Injective (e.visiblePoint ht) := by
  rintro ⟨i,q⟩ ⟨j,r⟩ h
  have hij : i = j := congrArg Sigma.fst h
  subst j
  have hqr := e.owner_injective ht i (eq_of_heq (Sigma.mk.inj h).2)
  cases hqr
  rfl

/-- The finite readout formula in D recovers exactly the original fine
pair relation among all reconstructed owners, through this ONE e. -/
theorem colour_readout (ht : B.Terminal) {i j : B.Sorts} (a : B.source.Atom i j)
    (q : D.VisibleTuple i) (r : D.VisibleTuple j) :
    D.colourReadout a q r ↔ B.source.atomRel a (e.owner ht q) (e.owner ht r) := by
  have he : D.colourReadout a q r ↔
      B.spectrumReadoutEval i (Sum.inl a)
        (originalOwnerMITuple B.source i (e.owner ht q))
        (originalOwnerMITuple B.source j (e.owner ht r)) := by
    constructor
    · intro h f hf
      exact (e.pair_transport f.2.2 (q.val f.1) (r.val f.2.1) _ _
        (e.owner_spec ht q f.1).symm (e.owner_spec ht r f.2.1).symm).mpr (h f hf)
    · intro h f hf
      exact (e.pair_transport f.2.2 (q.val f.1) (r.val f.2.1) _ _
        (e.owner_spec ht q f.1).symm (e.owner_spec ht r f.2.1).symm).mp (h f hf)
  exact he.trans (B.original_colour_readout _ ht (e.owner ht q) (e.owner ht r) a)

/-- Different whole realizations preserve EVERY original fine pair type
on the same finite visible tuple carrier, including equality endpoints. -/
theorem colour_independent (f : Realization D) (ht : B.Terminal)
    {i j : B.Sorts} (q : D.VisibleTuple i) (r : D.VisibleTuple j) :
    B.source.colour (e.owner ht q) (e.owner ht r) =
      B.source.colour (f.owner ht q) (f.owner ht r) := by
  apply Option.ext
  intro a
  exact (e.colour_readout ht a q r).symm.trans (f.colour_readout ht a q r)

def visibleTable (ht : B.Terminal) : Age.Table B.source D.VisiblePoint :=
  Age.table B.source (e.visiblePoint ht) (fun _ => 0)

/-- The reconstructed WHOLE finite visible object has one actual induced
realization in the original terminal owner source, not merely legal pairs. -/
theorem visibleTable_realized (ht : B.Terminal) :
    Age.Realized B.source (Age.zeroMask B.source) (e.visibleTable ht) :=
  ⟨e.visiblePoint ht,(fun _ => 0),e.visiblePoint_injective ht,
    ⟨fun _ => rfl,fun _ _ => ⟨rfl,rfl⟩⟩,rfl⟩

theorem visibleTable_independent (f : Realization D) (ht : B.Terminal) :
    e.visibleTable ht = f.visibleTable ht := by
  apply congrArg₂ OwnerTransversal.CountableColour.Table.mk
  · rfl
  · funext q r
    rcases q with ⟨i,q⟩
    rcases r with ⟨j,r⟩
    exact congrArg (fun c => Age.colourEquiv B.source (⟨i,j,c⟩ : Age.Colour B.source))
      (e.colour_independent f ht q r)

/-- A concrete finite chart in the actual owner age, obtained by enumerating
the finite visible tuple carrier after reconstructing it simultaneously. -/
def visibleChart (ht : B.Terminal) : Age.Chart B.source (Age.zeroMask B.source) := by
  letI := D.visiblePoint_finite
  letI : Fintype D.VisiblePoint := Fintype.ofFinite _
  let enum := (Fintype.equivFin D.VisiblePoint).symm
  exact Age.chartOf B.source (Age.reindex B.source (e.visibleTable ht) enum)
    (Age.realized_reindex B.source (e.visibleTable_realized ht) enum.toEmbedding)

private theorem chart_ext {C F : Age.Chart B.source (Age.zeroMask B.source)}
    (hs : C.size = F.size) (ht : HEq C.table F.table) : C = F := by
  cases C
  cases F
  cases hs
  cases eq_of_heq ht
  rfl

/-- Even the actual finite owner-age chart is independent of which whole
hidden realization supplied its witnesses. -/
theorem visibleChart_independent (f : Realization D) (ht : B.Terminal) :
    e.visibleChart ht = f.visibleChart ht := by
  apply chart_ext (C := e.visibleChart ht) (F := f.visibleChart ht) rfl
  dsimp only [visibleChart,Age.chartOf]
  rw [e.visibleTable_independent f ht]

end Realization
end FiniteHidden
end
end CCO.CloneTupleGeometry.OwnerStage
