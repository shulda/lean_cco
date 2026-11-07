import CCO.UnfilteredEP.FullLatticeKeys
import CCO.APRamseyReadout.CoordinateBridge
import CCO.ResetOrder.Hierarchy.Normalize
import CCO.UnarySupport.TypedTerms

/-!
# B064 C44: the actual proper-cut schedule and named finite-member keys

The task indices are exactly the named NONZERO proper MI quotients.
Logical equality is not made into a hidden coordinate. All strict coarser
proper MI kernels occur as parent keys; their rank decreases in the FULL
actual lattice. Upward key maps are evaluations of existing unary names
inside the actual finite member, including members with no real roots.
-/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w z
namespace CCO.UnfilteredEP
open CCO.APRamseyReadout CCO.CloneTupleGeometry CCO.ParityHasse.Original
open CCO.ResetOrder.Hierarchy CCO.UnaryTermsReturn CCO.TypedOrbitFrames
noncomputable section

variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)
local instance (i : B.Sorts) : Lattice (ColourEq (cloneSource B) i) := fullLattice B i
local instance (i : B.Sorts) : Fintype (ColourEq (cloneSource B) i) := Fintype.ofFinite _

abbrev HiddenCut := (i : B.Sorts) × NamedCoordinate B i

instance hiddenCut_finite : Finite (HiddenCut B) := by
  letI := B.source.finiteSort
  haveI (i : B.Sorts) : Finite (NamedCoordinate B i) :=
    CCO.TransitionClosure.original_named_hidden_coordinates_finite (cloneSource B) (HF B)
  infer_instance

abbrev CoarserCut (D : HiddenCut B) :=
  {E : NamedCoordinate B D.1 // D.2.val < E.val}

instance coarserCut_finite (D : HiddenCut B) : Finite (CoarserCut B D) := by
  haveI : Finite (NamedCoordinate B D.1) :=
    CCO.TransitionClosure.original_named_hidden_coordinates_finite (cloneSource B) (HF B)
  infer_instance

def coarserCutCount (D : HiddenCut B) : ℕ := Nat.card (CoarserCut B D)

def coarserCutEnumeration (D : HiddenCut B) :
    Fin (coarserCutCount B D) ≃ CoarserCut B D := by
  letI := Fintype.ofFinite (CoarserCut B D)
  unfold coarserCutCount
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.equivFin _).symm

def hiddenKeyCut (D : HiddenCut B) (a : Fin (coarserCutCount B D)) : HiddenCut B :=
  ⟨D.1,(coarserCutEnumeration B D a).val⟩

/-- Rank is measured in the entire FULL invariant lattice. -/
def hiddenCutRank (D : HiddenCut B) : ℕ := by
  letI := fullLattice B D.1
  letI := Fintype.ofFinite (ColourEq (cloneSource B) D.1)
  exact upperRank D.2.val

def actualCutSchedule : Schedule (HiddenCut B) where
  rank := hiddenCutRank B
  count := coarserCutCount B
  coordinate := hiddenKeyCut B
  coordinate_rank D a := by
    change upperRank (coarserCutEnumeration B D a).val.val < upperRank D.2.val
    exact upperRank_strict (coarserCutEnumeration B D a).property

abbrev hiddenCutSort (D : HiddenCut B) : (Sig B ht).Sorts :=
  coordinateSort B ht D.2

abbrev HiddenCutCarrier {V : Type z} (C : CCO.UnarySupport.Structure (Sig B ht) V)
    (D : HiddenCut B) := {x : V // C.sort x = hiddenCutSort B ht D}

/-- Literal existing upward function syntax between the two proper names. -/
def hiddenUpwardTerm {i : B.Sorts} (D E : NamedCoordinate B i) (hDE : D.val ≤ E.val) :
    CCO.UnarySupport.Structure.Term (Sig B ht)
      (coordinateSort B ht D) (coordinateSort B ht E) :=
  CCO.UnarySupport.Structure.Term.func (L := Sig B ht)
    (ULift.up (show OriginalCompletedPrimitiveSymbol (cloneSource B) (HF B) from
      .inr (.inl ⟨i,⟨(D,E),hDE⟩⟩))) (.var _)

variable {V : Type z} (C : CCO.UnarySupport.Structure (Sig B ht) V)
variable (hC : ActualAge B ht C)

/-- Totality is a proved consequence of actual-age membership. It is
applied at every proper input, independently of visible chart membership. -/
def hiddenUpwardValue (D : HiddenCut B) (a : Fin (coarserCutCount B D)) :
    HiddenCutCarrier B ht C D → HiddenCutCarrier B ht C (hiddenKeyCut B D a) :=
  C.value (CCO.TerminalHiddenHN.actualAge_total _ _ _ _ hC)
    (hiddenUpwardTerm B ht D.2 (coarserCutEnumeration B D a).val
      (coarserCutEnumeration B D a).property.le)

/-- The existing upward primitive has its literal quotient value in the
actual ambient partial structure. -/
theorem hiddenUpwardTerm_target {i : B.Sorts} (D E : NamedCoordinate B i)
    (hDE : D.val ≤ E.val) (q : Quotient D.val.val) :
    namedNode B E (Quot.mapRight hDE q) ∈
      (Target B ht).eval (hiddenUpwardTerm B ht D E hDE) (namedNode B D q) := by
  classical
  refine ⟨namedNode B D q,rfl,?_⟩
  change namedNode B E (Quot.mapRight hDE q) ∈
    (if (Hidden B ht).sort (namedNode B D q) = (Lang B ht).input
      (ULift.up (show OriginalCompletedPrimitiveSymbol (cloneSource B) (HF B) from
        .inr (.inl ⟨i,⟨(D,E),hDE⟩⟩))) then
      {(Hidden B ht).func (ULift.up (show OriginalCompletedPrimitiveSymbol (cloneSource B) (HF B) from
        .inr (.inl ⟨i,⟨(D,E),hDE⟩⟩))) (namedNode B D q)} else ∅)
  rw [if_pos (by rfl)]
  apply Set.mem_singleton_iff.mpr
  exact (original_completed_primitive_function_of_graph (cloneSource B) (HF B)
    (cloneSAP B) (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht))
    (.upward D E hDE q)).symm

/-- The finite member's named upward value agrees with its actual
quotient value under ANY supplied whole induced realization. -/
theorem hiddenUpwardValue_realization
    (e : C.Embedding (Target B ht)) (D : HiddenCut B)
    (a : Fin (coarserCutCount B D)) (x : HiddenCutCarrier B ht C D)
    (q : Quotient D.2.val.val) (hq : e.point x.val = namedNode B D.2 q) :
    e.point (hiddenUpwardValue B ht C hC D a x).val =
      namedNode B (coarserCutEnumeration B D a).val
        (Quot.mapRight (coarserCutEnumeration B D a).property.le q) := by
  apply (Target B ht).eval_functional
    (hiddenUpwardTerm B ht D.2 (coarserCutEnumeration B D a).val
      (coarserCutEnumeration B D a).property.le)
    (e.toHom.map_eval _ (C.value_mem _ _ x))
  rw [hq]
  exact hiddenUpwardTerm_target B ht D.2 (coarserCutEnumeration B D a).val
    (coarserCutEnumeration B D a).property.le q

/-- The actual parent fibre is defined by equality of its ENTIRE strict
coarser MI key. The ambient parent-quotient theorem below identifies this
with the true unique FULL cover, rather than a chosen subset of keys. -/
def actualCutSystem : System (actualCutSchedule B) (HiddenCutCarrier B ht C) where
  parent D x y := ∀ a, hiddenUpwardValue B ht C hC D a x = hiddenUpwardValue B ht C hC D a y
  parent_refl _ _ _ := rfl
  parent_symm := by intro i x y h a; exact (h a).symm
  parent_trans := by intro i x y z h h' a; exact (h a).trans (h' a)
  up := hiddenUpwardValue B ht C hC
  key_parent _ _ _ := Iff.rfl

/-- The syntactic ALL-coarser key relation is exactly equality in the
actual unique FULL parent quotient, under any whole realization. -/
theorem actualCutSystem_parent_realization
    (e : C.Embedding (Target B ht)) (D : HiddenCut B)
    (x y : HiddenCutCarrier B ht C D) (q r : Quotient D.2.val.val)
    (hq : e.point x.val = namedNode B D.2 q)
    (hr : e.point y.val = namedNode B D.2 r) :
    (actualCutSystem B ht C hC).parent D x y ↔
      Quot.mapRight (fullMIParent_cover B (fullMIOfNamed B D.1 D.2)).le q =
        Quot.mapRight (fullMIParent_cover B (fullMIOfNamed B D.1 D.2)).le r := by
  have hk := fullMIKey_eq_parent_iff B (fullMIOfNamed B D.1 D.2) q r
  constructor
  · intro h
    apply hk.mp
    intro L hDL hMI
    let E : NamedCoordinate B D.1 := namedCoordinateHF B ht D.1
      (strictCoarserFullMI B (fullMIOfNamed B D.1 D.2) L hDL hMI)
    let ec : CoarserCut B D := ⟨E,hDL⟩
    obtain ⟨a,ha⟩ := (coarserCutEnumeration B D).surjective ec
    have he := congrArg (fun z => e.point z.val) (h a)
    rw [hiddenUpwardValue_realization B ht C hC e D a x q hq,
      hiddenUpwardValue_realization B ht C hC e D a y r hr] at he
    have hclasses := namedNode_injective B (coarserCutEnumeration B D a).val he
    have hea : (coarserCutEnumeration B D a).val = E := congrArg Subtype.val ha
    have hkernel : (coarserCutEnumeration B D a).val.val = L :=
      congrArg Subtype.val hea
    induction q using Quotient.inductionOn with | _ q =>
      induction r using Quotient.inductionOn with | _ r =>
        apply Quotient.sound
        have hrel := Quotient.exact hclasses
        change (coarserCutEnumeration B D a).val.val q r at hrel
        exact hkernel ▸ hrel
  · intro h a
    apply Subtype.ext
    apply e.injective
    rw [hiddenUpwardValue_realization B ht C hC e D a x q hq,
      hiddenUpwardValue_realization B ht C hC e D a y r hr]
    apply congrArg (namedNode B (coarserCutEnumeration B D a).val)
    exact (hk.mpr h) (coarserCutEnumeration B D a).val.val
      (coarserCutEnumeration B D a).property
      (fullMIOfNamed B D.1 (coarserCutEnumeration B D a).val).property.2

/-- Any induced old map commutes with EVERY actual named upward key.
The whole arbitrary finite carrier is retained. -/
theorem actual_upward_embedding_commutes {W : Type*}
    {D : CCO.UnarySupport.Structure (Sig B ht) W} (hD : ActualAge B ht D)
    (e : C.Embedding D) (i : HiddenCut B) (a : Fin (coarserCutCount B i))
    (x : HiddenCutCarrier B ht C i) :
    e.point (hiddenUpwardValue B ht C hC i a x).val =
      (hiddenUpwardValue B ht D hD i a
        ⟨e.point x.val,(e.sort_eq x.val).trans x.property⟩).val :=
  e.value_map _ _ _ x

end
end CCO.UnfilteredEP
