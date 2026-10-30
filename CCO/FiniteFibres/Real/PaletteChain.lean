import CCO.FiniteFibres.Real.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-! C31/C34: all invariant equivalences are constant on the ACTUAL named
pair orbitals, and every strict chain step consumes a new diversity colour.
This argument does not import CCO, Hasse, exactness or a finite-size theorem. -/
universe v w t
namespace CCO.FiniteFibres.Real
open RealHull.Geometry

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))

def Invariant (E : Setoid M) : Prop :=
  ∀ (g : Aut S) (x y : M), E x y → E (g • x) (g • y)

variable {G : Type t} [Group G] [MulAction G M]

theorem invariant_colour (H : HomogeneousSource S G) (E : Setoid M)
    (hE : Invariant S E) (x y x' y' : M)
    (hc : S.colour (i := ()) (j := ()) x y = S.colour x' y') :
    E x y ↔ E x' y' := by
  obtain ⟨g,hgx,hgy⟩ := (actual_pair_orbit S H x y x' y').mp hc
  constructor
  · intro h
    simpa only [hgx,hgy] using hE g x y h
  · intro h
    have hh := hE g⁻¹ x' y' h
    rw [←hgx,←hgy] at hh
    simpa only [inv_smul_smul] using hh

structure InvariantChain (m : ℕ) where
  equivalence : Fin (m+1) → Setoid M
  invariant : ∀ i, Invariant S (equivalence i)
  monotone : Monotone equivalence
  strict : ∀ i : Fin m, equivalence i.castSucc < equivalence i.succ

namespace InvariantChain
variable {S} {m : ℕ} (C : InvariantChain S m)

private theorem step_witness (i : Fin m) : ∃ x y : M,
    C.equivalence i.succ x y ∧ ¬ C.equivalence i.castSucc x y := by
  by_contra hn
  apply (C.strict i).not_ge
  intro x y hxy
  by_contra hnot
  exact hn ⟨x,y,hxy,hnot⟩

structure Increment (i : Fin m) where
  left : M
  right : M
  member : C.equivalence i.succ left right
  absent : ¬ C.equivalence i.castSucc left right
  atom : Atom S
  edge : col S left right = some atom

noncomputable def increment (i : Fin m) : C.Increment i := by
  classical
  apply Classical.choice
  obtain ⟨x,y,hxy,hnot⟩ := C.step_witness i
  have hne : x ≠ y := by
    intro he
    subst y
    exact hnot ((C.equivalence i.castSucc).refl x)
  obtain ⟨a,ha⟩ := col_some_of_ne S hne
  exact ⟨⟨x,y,hxy,hnot,a,ha⟩⟩

theorem increment_atom_ne (H : HomogeneousSource S G) {i j : Fin m} (hij : i < j) :
    (C.increment i).atom ≠ (C.increment j).atom := by
  intro hcol
  have hij' : i.succ ≤ j.castSucc := by
    change i.val + 1 ≤ j.val
    exact Nat.succ_le_of_lt hij
  have hmem : C.equivalence j.castSucc (C.increment i).left (C.increment i).right :=
    C.monotone hij' (C.increment i).member
  have heq : col S (C.increment i).left (C.increment i).right =
      col S (C.increment j).left (C.increment j).right :=
    (C.increment i).edge.trans ((congrArg some hcol).trans (C.increment j).edge.symm)
  exact (C.increment j).absent ((invariant_colour S H _ (C.invariant j.castSucc) _ _ _ _ heq).mp hmem)

theorem increment_atom_injective (H : HomogeneousSource S G) :
    Function.Injective (fun i : Fin m => (C.increment i).atom) := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact C.increment_atom_ne H hlt hij
  · exact C.increment_atom_ne H hgt hij.symm

/-- Every strict homogeneous invariant chain has at most as many steps as
the actual original diversity palette. In particular this holds for every
saturated Id-to-top Hasse chain supplied by the finite group argument. -/
theorem length_le_palette (C : InvariantChain S m) (H : HomogeneousSource S G) :
    m ≤ Nat.card (Atom S) := by
  letI := S.finiteAtom () ()
  simpa only [Nat.card_fin] using
    Nat.card_le_card_of_injective _ (increment_atom_injective (C := C) H)

end InvariantChain

theorem fibre_palette_card_le [DecidableEq M] (A : Finset M) (q : ↥A → Atom S) :
    Nat.card (InducedAtom S () (FibreSet S A q)) ≤ Nat.card (Atom S) := by
  letI := S.finiteAtom () ()
  exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective

end CCO.FiniteFibres.Real
