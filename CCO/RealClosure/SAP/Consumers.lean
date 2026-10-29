import CCO.RealClosure.SAP.InfiniteHelly

/-! Actual source consumers, including the accepted finite packet and
minimal-direction notation, plus empty/singleton/identity boundary cases. -/
universe v w t
namespace CCO.RealClosure.SAP
open ParityHasse.Original
variable {M : Type v} {G : Type t} [Group G] [MulAction G M]

/-- Nonsymmetric C19–24 export: ordinary original source homogeneity and
actual age SAP discharge all orbit, monolith and full-MI providers. -/
theorem nonsymmetric_source_core (S : Source.{v,w} M) (H : S.Homogeneous (G := G))
    (sap : S.AgeSAP) [Infinite M] (A : Finset M) (x : M) :
    Bounds.Acl G A = (A : Set M) ∧
    InvariantEq.IsMonolith (InvariantEq.monolith : InvariantEq G M) ∧
    Set.Infinite {y | (InvariantEq.monolith : InvariantEq G M) x y} ∧
    {y | InvariantEq.tuple (G := G) y = InvariantEq.tuple x} =
      {y | (InvariantEq.monolith : InvariantEq G M) x y} ∧
    Set.Infinite {y | ∃ g : G, g ∈ InvariantEq.tupleStabilizer x ∧ g • x = y} :=
  ⟨Source.acl_eq_base S H sap A,InvariantEq.monolith_property S H sap,
    InvariantEq.monolith_class_infinite S H sap x,
    InvariantEq.tuple_fibre_eq S H sap x,
    InvariantEq.tuple_stabilizer_orbit_infinite S H sap x⟩

/-- Primitive means that the FULL original invariant lattice has only
identity and Top. Its actual proper nonidentity MI coordinate type is empty. -/
theorem primitive_empty_MI
    (primitive : ∀ E : InvariantEq G M, E = ⊥ ∨ E = ⊤) :
    IsEmpty (InvariantEq.NonidentityMI G M) := by
  constructor
  intro J
  rcases primitive J.val with h | h
  · exact J.property.1 h
  · exact J.property.2.ne_top h

theorem primitive_real_fibre
    (primitive : ∀ E : InvariantEq G M, E = ⊥ ∨ E = ⊤) (x : M) :
    {y | InvariantEq.tuple (G := G) y = InvariantEq.tuple x} = Set.univ := by
  letI := primitive_empty_MI primitive
  exact InvariantEq.empty_mi_fibre x

variable (S : AtomicSource.{0,v,w} Unit (fun _ => M)) (H : HomogeneousSource S G)
include H

def colourMonolith : ColourEq S () :=
  invariantColourIso S H (InvariantEq.monolith : InvariantEq G M)

theorem colourMonolith_ne_bot (sap : AgeSAP S) [Infinite M] : colourMonolith S H ≠ ⊥ := by
  intro h
  have ht := congrArg (invariantColourIso S H).symm h
  have hm := (InvariantEq.monolith_property (atomicSource S)
    (atomic_homogeneous S H) (atomic_sap S sap)).1
  apply hm
  simpa only [colourMonolith,OrderIso.symm_apply_apply,OrderIso.map_bot] using ht

theorem colourMonolith_le (E : ColourEq S ()) (hE : E ≠ ⊥) : colourMonolith S H ≤ E := by
  have hn : (invariantColourIso S H).symm E ≠ ⊥ := by
    intro h
    apply hE
    have ht := congrArg (invariantColourIso S H) h
    simpa only [OrderIso.apply_symm_apply,OrderIso.map_bot] using ht
  exact InvariantEq.monolith_le hn

theorem colourMonolith_infinite (sap : AgeSAP S) [Infinite M] (x : M) :
    Set.Infinite {y | colourMonolith S H x y} :=
  InvariantEq.monolith_class_infinite (atomicSource S)
    (atomic_homogeneous S H) (atomic_sap S sap) x

theorem finiteClasses_iff_identity (sap : AgeSAP S) (E : ColourEq S ()) :
    Bounds.FiniteClasses S E ↔ E = ⊥ := by
  constructor
  · intro hf
    obtain ⟨x⟩ := S.nonemptySort ()
    by_contra hn
    exact colour_class_infinite S H sap hn x (Set.finite_coe_iff.mp (hf x))
  · rintro rfl
    exact Bounds.finiteClasses_bot S

/-- The already accepted GREATEST finite packet is exactly original real
identity. No packet exactness or real-closure converse is used. -/
theorem finitePacket_identity (sap : AgeSAP S) : Bounds.finitePacket S H = ⊥ :=
  (finiteClasses_iff_identity S H sap _).mp (Bounds.finitePacket_finite S H)

theorem direction_eq_monolith (sap : AgeSAP S) [Infinite M] (D : Bounds.Direction S) :
    D.val = colourMonolith S H := by
  have hn : D.val ≠ ⊥ := by
    intro h
    apply D.property.1
    rw [h]
    exact Bounds.finiteClasses_bot S
  apply le_antisymm ?_ (colourMonolith_le S H D.val hn)
  by_contra hnot
  have hlt : colourMonolith S H < D.val :=
    lt_of_le_of_ne (colourMonolith_le S H D.val hn) (Ne.symm (ne_of_not_le hnot))
  have hf := D.property.2 (colourMonolith S H) hlt
  exact colourMonolith_ne_bot S H sap ((finiteClasses_iff_identity S H sap _).mp hf)

/-- In the notation of the accepted real closure package, r=1. -/
theorem directionCount_one (sap : AgeSAP S) [Infinite M] : Bounds.directionCount S = 1 := by
  letI : Nonempty (Bounds.Direction S) := Bounds.direction_nonempty_of_infinite S
  letI : Subsingleton (Bounds.Direction S) := ⟨by
    intro D E
    apply Subtype.ext
    exact (direction_eq_monolith S H sap D).trans (direction_eq_monolith S H sap E).symm⟩
  exact Nat.card_unique

theorem sap_acl_dcl (sap : AgeSAP S) (A : Finset M) :
    Bounds.Acl G A = (A : Set M) ∧ Bounds.Dcl G A = (A : Set M) := by
  have ha := Source.acl_eq_base (atomicSource S) (atomic_homogeneous S H) (atomic_sap S sap) A
  refine ⟨ha,Set.Subset.antisymm ?_ (fun _ hx => Bounds.parameter_mem_dcl A hx)⟩
  intro x hx
  rw [← ha]
  exact Bounds.dcl_subset_acl A hx

/-- Empty family really has ambient Top kernel and infinite intersection. -/
theorem empty_family_boundary [Infinite M] :
    familyEquiv S H (fun k : Fin 0 => Fin.elim0 k : Fin 0 → ColourEq S ()) = ⊤ ∧
    Set.Infinite {y : M | ∀ k : Fin 0, (Fin.elim0 k : ColourEq S ()) y y} := by
  constructor
  · apply ColourEq.ext
    intro x y
    exact iff_of_true (fun k => Fin.elim0 k) trivial
  · have hu : {y : M | ∀ k : Fin 0, (Fin.elim0 k : ColourEq S ()) y y} = Set.univ := by
      ext y
      exact iff_of_true (fun k => Fin.elim0 k) trivial
    rw [hu]
    exact Set.infinite_univ

/-- The common kernel is itself nonidentity, as required by C29. -/
theorem familyEquiv_ne_identity (sap : AgeSAP S) [Infinite M]
    {I : Type*} (E : I → ColourEq S ()) (hne : ∀ k, E k ≠ ⊥) :
    familyEquiv S H E ≠ ⊥ := by
  intro h
  let x : M := Classical.choice inferInstance
  have hi := family_class_infinite S H sap E hne x
  rw [h] at hi
  apply hi
  change Set.Finite {y : M | x = y}
  simpa only [Set.setOf_eq_eq_singleton'] using Set.finite_singleton x

/-- One nonidentity class is infinite even though pairwise compatibility
is vacuous. An identity class is instead exactly its real singleton. -/
theorem singleton_identity_boundary (sap : AgeSAP S) (E : ColourEq S ()) (x : M) :
    (E ≠ ⊥ → Set.Infinite {y | E x y}) ∧
    {y | (⊥ : ColourEq S ()) x y} = {x} := by
  refine ⟨fun h => colour_class_infinite S H sap h x,?_⟩
  ext y
  exact eq_comm

end CCO.RealClosure.SAP
