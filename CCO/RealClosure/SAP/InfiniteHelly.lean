import CCO.RealClosure.SAP.AtomicBridge
import CCO.RealClosure.Bounds.TerminalLattice

/-! C29–31: different-centre actual exact class Helly followed by the
independent SAP size argument. Full NR2 is used only to discharge exactness
in the terminal upgrade. Equality kernels are excluded; the empty family
is the entire original infinite sort. -/
universe v w t z
namespace CCO.RealClosure.SAP
open ParityHasse.Original ExactCRT
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
include H

def familyEquiv {I : Type z} (E : I → ColourEq S ()) : ColourEq S () :=
  invariantColourIso S H
    (InvariantEq.familyMeet (fun k => (invariantColourIso S H).symm (E k)))

@[simp] theorem familyEquiv_apply {I : Type z} (E : I → ColourEq S ()) (x y : M) :
    familyEquiv S H E x y ↔ ∀ k, E k x y := Iff.rfl

theorem colour_class_infinite (sap : AgeSAP S) {E : ColourEq S ()}
    (hE : E ≠ ⊥) (x : M) : Set.Infinite {y | E x y} := by
  have hn : (invariantColourIso S H).symm E ≠ ⊥ := by
    intro he
    apply hE
    have h := congrArg (invariantColourIso S H) he
    simpa only [OrderIso.apply_symm_apply,OrderIso.map_bot] using h
  exact InvariantEq.class_infinite (atomicSource S) (atomic_homogeneous S H)
    (atomic_sap S sap) hn x

theorem family_class_infinite (sap : AgeSAP S) [Infinite M]
    {I : Type z} (E : I → ColourEq S ()) (hne : ∀ k, E k ≠ ⊥) (x : M) :
    Set.Infinite {y | familyEquiv S H E x y} := by
  apply (InvariantEq.monolith_class_infinite (atomicSource S)
    (atomic_homogeneous S H) (atomic_sap S sap) x).mono
  intro y hy k
  have hn : (invariantColourIso S H).symm (E k) ≠ ⊥ := by
    intro he
    apply hne k
    have h := congrArg (invariantColourIso S H) he
    simpa only [OrderIso.apply_symm_apply,OrderIso.map_bot] using h
  exact InvariantEq.monolith_le hn hy

theorem class_intersection_eq {I : Type z} (E : I → ColourEq S ())
    (centre : I → M) {x : M} (hx : ∀ k, E k (centre k) x) :
    {y | ∀ k, E k (centre k) y} = {y | familyEquiv S H E x y} := by
  ext y
  constructor
  · intro hy k
    exact (E k).val.trans ((E k).val.symm (hx k)) (hy k)
  · intro hy k
    exact (E k).val.trans (hx k) (hy k)

/-- C29: the common set is ONE entire actual class, and is infinite.
The nonemptiness provider is accepted B002/B008 BALL Helly at the actual
different centres, rather than support intersection. -/
theorem infinite_exact_class_helly (sap : AgeSAP S) [Infinite M]
    (cco : SemanticCCO.{0,v,v,w} S) {I : Type z} [Finite I]
    (E : I → ColourEq S ()) (centre : I → M)
    (hexact : ∀ k, IsExactEq S (i := ()) (E k).val) (hne : ∀ k, E k ≠ ⊥)
    (hp : ∀ j k, ∃ x, E j (centre j) x ∧ E k (centre k) x) :
    ∃ x : M, (∀ k, E k (centre k) x) ∧
      {y | ∀ k, E k (centre k) y} = {y | familyEquiv S H E x y} ∧
      Set.Infinite {y | ∀ k, E k (centre k) y} := by
  obtain ⟨x,hx⟩ := exactEq_classHelly S H cco
    (fun k => (⟨(E k).val,hexact k⟩ : ExactEq S H cco ())) centre hp
  have heq := class_intersection_eq S H E centre hx
  refine ⟨x,hx,heq,?_⟩
  rw [heq]
  exact family_class_infinite S H sap E hne x

/-- C30: full original NR2 supplies every exactness obligation through the
accepted CCO-free single RAW word theorem; no quotient SAP is imported. -/
theorem infinite_terminal_class_helly (sap : AgeSAP S) [Infinite M]
    (cco : SemanticCCO.{0,v,v,w} S) (nr2 : Bounds.SortNR2 S ())
    {I : Type z} [Finite I] (E : I → ColourEq S ()) (centre : I → M)
    (hne : ∀ k, E k ≠ ⊥)
    (hp : ∀ j k, ∃ x, E j (centre j) x ∧ E k (centre k) x) :
    ∃ x : M, (∀ k, E k (centre k) x) ∧
      {y | ∀ k, E k (centre k) y} = {y | familyEquiv S H E x y} ∧
      Set.Infinite {y | ∀ k, E k (centre k) y} :=
  infinite_exact_class_helly S H sap cco E centre
    (fun k => Bounds.terminal_all_exact S H nr2 (E k)) hne hp

def MICompatible (q : InvariantEq.Tuple G M) : Prop :=
  ∀ J K : InvariantEq.NonidentityMI G M, ∃ x : M,
    Quotient.mk J.val.val x = q J ∧ Quotient.mk K.val.val x = q K

/-- C31: ALL proper nonidentity FULL-lattice MI coordinates are realized
iff pairwise compatible. Its entire fibre is one infinite monolith class
and its pointwise tuple stabilizer has precisely that infinite real orbit. -/
theorem terminal_mi_realization (sap : AgeSAP S) [Infinite M]
    (cco : SemanticCCO.{0,v,v,w} S) (nr2 : Bounds.SortNR2 S ())
    (q : InvariantEq.Tuple G M) :
    (∃ x : M, InvariantEq.tuple x = q) ↔ MICompatible q := by
  constructor
  · rintro ⟨x,rfl⟩ J K
    exact ⟨x,rfl,rfl⟩
  · intro hp
    classical
    letI := InvariantEq.finite (atomicSource S) (atomic_homogeneous S H)
    let J : InvariantEq.NonidentityMI G M → ColourEq S () :=
      fun k => invariantColourIso S H k.val
    let centre : InvariantEq.NonidentityMI G M → M := fun k => (q k).out
    have hc (k : InvariantEq.NonidentityMI G M) :
        Quotient.mk k.val.val (centre k) = q k := Quotient.out_eq _
    have hne : ∀ k, J k ≠ ⊥ := by
      intro k he
      apply k.property.1
      have ht := congrArg (invariantColourIso S H).symm he
      simpa only [J,OrderIso.symm_apply_apply,OrderIso.map_bot] using ht
    have hpair : ∀ j k, ∃ x, J j (centre j) x ∧ J k (centre k) x := by
      intro j k
      obtain ⟨x,hj,hk⟩ := hp j k
      exact ⟨x,Quotient.exact ((hc j).trans hj.symm),
        Quotient.exact ((hc k).trans hk.symm)⟩
    obtain ⟨x,hx,_,_⟩ := infinite_terminal_class_helly S H sap cco nr2 J centre hne hpair
    refine ⟨x,funext (fun k => ?_)⟩
    exact (Quotient.sound ((k.val.val.symm (hx k)))).trans (hc k)

theorem terminal_mi_infinite_fibre (sap : AgeSAP S) [Infinite M]
    (cco : SemanticCCO.{0,v,v,w} S) (nr2 : Bounds.SortNR2 S ())
    (q : InvariantEq.Tuple G M) (hp : MICompatible q) :
    ∃ x : M, InvariantEq.tuple x = q ∧
      {y | InvariantEq.tuple (G := G) y = q} =
        {y | (InvariantEq.monolith : InvariantEq G M) x y} ∧
      Set.Infinite {y | InvariantEq.tuple (G := G) y = q} ∧
      Set.Infinite {y | ∃ g : G, g ∈ InvariantEq.tupleStabilizer x ∧ g • x = y} := by
  obtain ⟨x,rfl⟩ := (terminal_mi_realization S H sap cco nr2 q).mpr hp
  exact ⟨x,rfl,InvariantEq.tuple_fibre_eq (atomicSource S) (atomic_homogeneous S H)
    (atomic_sap S sap) x,
    InvariantEq.tuple_fibre_infinite (atomicSource S) (atomic_homogeneous S H)
      (atomic_sap S sap) x,
    InvariantEq.tuple_stabilizer_orbit_infinite (atomicSource S) (atomic_homogeneous S H)
      (atomic_sap S sap) x⟩

end CCO.RealClosure.SAP
