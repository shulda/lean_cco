import CCO.ExactCRT.ExactLattice
import CCO.ExactCRT.AbstractCoordinates

/-!
# B008 C13–14: actual exact distributivity, CRT and Birkhoff

Every provider here is instantiated from original homogeneity and semantic
CCO. There is no SAP, countability, Hasse/parity, finite-index or
full-invariant-lattice distributivity premise. The use of the existing
`ColourEq` finite-palette injection in `ExactLattice` is elementary algebra,
not a dependency on the Hasse theorem. -/

universe u v w t z
namespace CCO.ExactCRT
open RawExact
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G)
variable (cco : SemanticCCO.{u,v,max u v,w} S)

/-- The actual source supplies every represented commutation premise. -/
theorem exact_commutes (i : ι) : Abstract.Commutes (exactSublattice S H cco i) :=
  exactEq_commutes S H cco i

/-- Actual different-centre exact BALL Helly supplies the abstract class law. -/
theorem exact_classHelly (i : ι) : Abstract.ClassHelly (exactSublattice S H cco i) :=
  fun _ E centre pair => exactEq_classHelly S H cco E centre pair

/-- C13: the finite exact sublattice is distributive, with its inherited
actual setoid meet and join. This asserts nothing about all invariants. -/
@[instance_reducible] def exactDistribLattice (i : ι) : DistribLattice (ExactEq S H cco i) :=
  Abstract.distribLattice_of_helly (exactSublattice S H cco i)
    (exact_commutes S H cco i) (exact_classHelly S H cco i)

/-- Finite set-level CRT includes empty, singleton and repeated families.
Its kernel is the ACTUAL intersection of the original equivalences. -/
noncomputable def exactCRT (i : ι) {I : Type z} [Finite I]
    (E : I → ExactEq S H cco i) :
    Quotient (Abstract.familyMeet (fun k => (E k).val)) ≃
      {q : ∀ k, Quotient (E k).val // Abstract.Compatible (fun k => (E k).val) q} :=
  Abstract.crtEquiv (exactSublattice S H cco i)
    (exact_commutes S H cco i) (exact_classHelly S H cco i) E

@[simp] theorem exactCRT_apply (i : ι) {I : Type z} [Finite I]
    (E : I → ExactEq S H cco i) (x : X i) (k : I) :
    (exactCRT S H cco i E (Quotient.mk _ x)).val k = Quotient.mk (E k).val x := rfl

/-- Every compatible finite actual quotient tuple has one real representative. -/
theorem exactCRT_real_representative (i : ι) {I : Type z} [Finite I]
    (E : I → ExactEq S H cco i) (q : ∀ k, Quotient (E k).val)
    (hq : Abstract.Compatible (fun k => (E k).val) q) :
    ∃ x : X i, ∀ k, Quotient.mk (E k).val x = q k := by
  obtain ⟨r, hr⟩ := (exactCRT S H cco i E).surjective ⟨q, hq⟩
  induction r using Quotient.inductionOn with
  | _ x => exact ⟨x, fun k => congrFun (congrArg Subtype.val hr) k⟩

/-- C14: Birkhoff represents actual exact equivalences by downsets of
NONZERO join-irreducibles, rather than atoms or meet-irreducibles. -/
noncomputable def exactBirkhoff (i : ι) :
    ExactEq S H cco i ≃o LowerSet (FiniteOrder.JoinIrreducible (ExactEq S H cco i)) := by
  letI : DistribLattice (ExactEq S H cco i) := exactDistribLattice S H cco i
  exact FiniteOrder.birkhoff

@[simp] theorem mem_exactBirkhoff (i : ι) (E : ExactEq S H cco i)
    (p : FiniteOrder.JoinIrreducible (ExactEq S H cco i)) :
    p ∈ exactBirkhoff S H cco i E ↔ p.val ≤ E := Iff.rfl

/-- The inverse coordinate map is the literal finite join of a downset. -/
noncomputable def exactDownJoin (i : ι)
    (D : LowerSet (FiniteOrder.JoinIrreducible (ExactEq S H cco i))) :
    ExactEq S H cco i := by
  letI : DistribLattice (ExactEq S H cco i) := exactDistribLattice S H cco i
  exact FiniteOrder.downJoin D

@[simp] theorem exactBirkhoff_inverse (i : ι)
    (D : LowerSet (FiniteOrder.JoinIrreducible (ExactEq S H cco i))) :
    (exactBirkhoff S H cco i).symm D = exactDownJoin S H cco i D := by
  rfl

/-- C16 as an actual source consumer: a selected coordinate maps ONTO
its MI quotient. No fine-colour reconstruction or action lifting is inferred. -/
theorem exact_selected_coordinate_image (i : ι)
    (head : ExactEq S H cco i) (tail : List (ExactEq S H cco i))
    (L : ExactEq S H cco i) (hL : FiniteOrder.BinaryMeetIrreducible L)
    (hle : FiniteOrder.listMeet head tail ≤ L) :
    ∃ J ∈ head :: tail, ∃ f : Quotient J.val → Quotient L.val,
      Function.Surjective f ∧ ∀ x, f (Quotient.mk _ x) = Quotient.mk _ x :=
  Abstract.selected_coordinate_image (exactSublattice S H cco i)
    (Abstract.inf_sup_le_of_helly _ (exact_commutes S H cco i) (exact_classHelly S H cco i))
    head tail L hL hle

/-- A separate actual two-factor set consumer; its proof uses neither
full class Helly nor distributivity, only actual represented commutation. -/
noncomputable def exactFibreProduct (i : ι) (E F : ExactEq S H cco i) :
    Quotient (E.val ⊓ F.val) ≃ Abstract.FibreProduct E.val F.val :=
  Abstract.fibreProductEquiv E.val F.val (exact_commutes S H cco i E F)

include S in
/-- Empty quotient coordinates have ambient Top as kernel. -/
theorem exact_empty_CRT (i : ι) :
    Function.Bijective (Abstract.compatibleCoordinates
      (fun k : Fin 0 => Fin.elim0 k : Fin 0 → Setoid (X i))) := by
  let : Nonempty (X i) := S.nonemptySort i
  exact Abstract.empty_coordinates_bijective

/-- Repeated actual coordinates impose no extra realization premise. -/
theorem exact_repeated_coordinates (i : ι) (E : ExactEq S H cco i)
    (q : ∀ _ : Fin 3, Quotient E.val)
    (compatible : Abstract.Compatible (fun _ : Fin 3 => E.val) q) :
    ∃ x : X i, ∀ k : Fin 3, Quotient.mk E.val x = q k :=
  exactCRT_real_representative S H cco i (fun _ => E) q compatible

/-- If the exact lattice has one element, its Birkhoff poset is empty. -/
theorem exact_singleton_irreducibles_empty (i : ι) [Subsingleton (ExactEq S H cco i)] :
    IsEmpty (FiniteOrder.JoinIrreducible (ExactEq S H cco i)) := by
  let : DistribLattice (ExactEq S H cco i) := exactDistribLattice S H cco i
  exact FiniteOrder.no_irreducibles_of_subsingleton

end CCO.ExactCRT
