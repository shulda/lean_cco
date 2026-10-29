import CCO.ExactCRT.SourceLattice
import CCO.Owners.Product.SourceGeometry

/-!
The actual exact quotient coordinates used by the finite owner recursion.
All indices are finite sets of NONZERO join-irreducibles; the lattice
identities are asserted for genuine upsets. Invalid indices are harmless
auxiliary objects and carry no stage invariant.
-/

universe v w t
namespace CCO.Owners.Master

noncomputable section

open RawExact ExactCRT

variable {A : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)

abbrev Exact : Type v := ExactEq S H cco ()
abbrev Position : Type v := FiniteOrder.JoinIrreducible (Exact S H cco)

instance exactFinite : Finite (Exact S H cco) := exactEqFinite S H cco ()
instance exactOrderBot : OrderBot (Exact S H cco) := exactEqOrderBot S H cco ()
instance exactOrderTop : OrderTop (Exact S H cco) := exactEqOrderTop S H cco ()
noncomputable instance exactFintype : Fintype (Exact S H cco) := Fintype.ofFinite _
noncomputable instance positionFintype : Fintype (Position S H cco) := Fintype.ofFinite _
noncomputable instance positionDecidableEq : DecidableEq (Position S H cco) := Classical.decEq _

noncomputable def coordinateKernel (V : Finset (Position S H cco)) : Exact S H cco := by
  classical
  exact (Finset.univ \ V).sup Subtype.val

theorem coordinateKernel_antitone {V W : Finset (Position S H cco)} (hWV : W ⊆ V) :
    coordinateKernel S H cco V ≤ coordinateKernel S H cco W := by
  classical
  unfold coordinateKernel
  apply Finset.sup_le
  intro p hp
  apply Finset.le_sup (f := Subtype.val)
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ p, fun h =>
    (Finset.mem_sdiff.mp hp).2 (hWV h)⟩

@[simp] theorem coordinateKernel_univ :
    coordinateKernel S H cco Finset.univ = ⊥ := by
  classical
  simp [coordinateKernel]

/-- Membership of the Birkhoff downset is precisely the complement of
the chosen upward closed coordinate set. -/
theorem position_le_coordinateKernel (V : Finset (Position S H cco))
    (upV : ∀ ⦃p q : Position S H cco⦄, p ∈ V → p ≤ q → q ∈ V)
    (p : Position S H cco) :
    p.val ≤ coordinateKernel S H cco V ↔ p ∉ V := by
  classical
  letI := exactDistribLattice S H cco ()
  rw [coordinateKernel,
    FiniteOrder.join_irreducible_finite_prime _ _ p.property]
  constructor
  · rintro ⟨q,hq,hpq⟩ hp
    exact (Finset.mem_sdiff.mp hq).2 (upV hp hpq)
  · intro hp
    exact ⟨p,Finset.mem_sdiff.mpr ⟨Finset.mem_univ p,hp⟩,le_rfl⟩

theorem coordinateKernel_empty : coordinateKernel S H cco ∅ = ⊤ := by
  apply (exactBirkhoff S H cco ()).injective
  ext p
  change p.val ≤ coordinateKernel S H cco ∅ ↔ p.val ≤ ⊤
  rw [position_le_coordinateKernel S H cco ∅ (by simp)]
  simp

theorem coordinateKernel_union (V W : Finset (Position S H cco))
    (upV : ∀ ⦃p q : Position S H cco⦄, p ∈ V → p ≤ q → q ∈ V)
    (upW : ∀ ⦃p q : Position S H cco⦄, p ∈ W → p ≤ q → q ∈ W) :
    coordinateKernel S H cco (V ∪ W) =
      coordinateKernel S H cco V ⊓ coordinateKernel S H cco W := by
  classical
  apply (exactBirkhoff S H cco ()).injective
  ext p
  change p.val ≤ coordinateKernel S H cco (V ∪ W) ↔
    p.val ≤ coordinateKernel S H cco V ⊓ coordinateKernel S H cco W
  rw [position_le_coordinateKernel S H cco (V ∪ W) (by
    intro p q hp hpq
    rcases Finset.mem_union.mp hp with hp | hp
    · exact Finset.mem_union_left _ (upV hp hpq)
    · exact Finset.mem_union_right _ (upW hp hpq)), le_inf_iff,
    position_le_coordinateKernel S H cco V upV,
    position_le_coordinateKernel S H cco W upW]
  simp

theorem coordinateKernel_inter (V W : Finset (Position S H cco))
    (upV : ∀ ⦃p q : Position S H cco⦄, p ∈ V → p ≤ q → q ∈ V)
    (upW : ∀ ⦃p q : Position S H cco⦄, p ∈ W → p ≤ q → q ∈ W) :
    coordinateKernel S H cco (V ∩ W) =
      coordinateKernel S H cco V ⊔ coordinateKernel S H cco W := by
  classical
  letI := exactDistribLattice S H cco ()
  apply (exactBirkhoff S H cco ()).injective
  ext p
  change p.val ≤ coordinateKernel S H cco (V ∩ W) ↔
    p.val ≤ coordinateKernel S H cco V ⊔ coordinateKernel S H cco W
  rw [position_le_coordinateKernel S H cco (V ∩ W) (by
    intro p q hp hpq
    exact Finset.mem_inter.mpr ⟨upV (Finset.mem_inter.mp hp).1 hpq,
      upW (Finset.mem_inter.mp hp).2 hpq⟩),
    FiniteOrder.join_irreducible_prime p.property,
    position_le_coordinateKernel S H cco V upV,
    position_le_coordinateKernel S H cco W upW]
  simp only [Finset.mem_inter, not_and_or]

abbrev Coordinate (V : Finset (Position S H cco)) :=
  Quotient (coordinateKernel S H cco V).val

instance coordinateInvariant (V : Finset (Position S H cco)) :
    RawExact.CanonicalQuotients.Invariant G (coordinateKernel S H cco V).val :=
  Product.exactInvariant S H cco _

def coordinateProjection (V : Finset (Position S H cco)) : A → Coordinate S H cco V :=
  Quotient.mk''

def coordinateMap {V W : Finset (Position S H cco)} (hWV : W ⊆ V) :
    Coordinate S H cco V → Coordinate S H cco W :=
  Abstract.quotientMap (coordinateKernel_antitone S H cco hWV)

@[simp] theorem coordinateMap_projection {V W : Finset (Position S H cco)}
    (hWV : W ⊆ V) (a : A) :
    coordinateMap S H cco hWV (coordinateProjection S H cco V a) =
      coordinateProjection S H cco W a := rfl

theorem coordinateMap_surjective {V W : Finset (Position S H cco)} (hWV : W ⊆ V) :
    Function.Surjective (coordinateMap S H cco hWV) :=
  Abstract.quotientMap_surjective _

theorem coordinateMap_id (V : Finset (Position S H cco)) (x : Coordinate S H cco V) :
    coordinateMap S H cco (Finset.Subset.refl V) x = x := by
  induction x using Quotient.inductionOn with | _ a => rfl

theorem coordinateMap_comp {U V W : Finset (Position S H cco)}
    (hVU : V ⊆ U) (hWV : W ⊆ V) (x : Coordinate S H cco U) :
    coordinateMap S H cco hWV (coordinateMap S H cco hVU x) =
      coordinateMap S H cco (hWV.trans hVU) x := by
  induction x using Quotient.inductionOn with | _ a => rfl

theorem coordinateMap_equivariant {V W : Finset (Position S H cco)}
    (hWV : W ⊆ V) (g : G) (x : Coordinate S H cco V) :
    coordinateMap S H cco hWV (g • x) = g • coordinateMap S H cco hWV x := by
  induction x using Quotient.inductionOn with | _ a => rfl

end
end CCO.Owners.Master
