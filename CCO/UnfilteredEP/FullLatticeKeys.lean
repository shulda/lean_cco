import CCO.APRamseyReadout.ActualSource
import CCO.ResetOrder.Hierarchy.Quotients
import CCO.RealClosure.Bounds.TerminalLattice
import Mathlib.Data.Fintype.EquivFin

/-! Actual FULL clone equivalences and the complete coarser-coordinate
key. The terminal distributivity source is independent of Ramsey and EP.
The top-cover case correctly has an empty key. -/

universe u v w
namespace CCO.UnfilteredEP
open CCO.APRamseyReadout CCO.CloneTupleGeometry CCO.ParityHasse.Original
open CCO.ResetOrder.Hierarchy
noncomputable section
variable (B : OwnerStage.{u,v,w})

@[instance_reducible] def fullLattice (i : B.Sorts) :
    Lattice (ColourEq (cloneSource B) i) :=
  ColourEq.lattice (cloneSource B) (cloneHomogeneous B)

local instance (i : B.Sorts) : Lattice (ColourEq (cloneSource B) i) := fullLattice B i
local instance (i : B.Sorts) : Fintype (ColourEq (cloneSource B) i) := Fintype.ofFinite _

/-- C43/I27: the FULL invariant lattice is distributive because every
FULL equivalence is actual RAW exact at this genuine terminal endpoint. -/
@[instance_reducible] def terminalFullDistrib (ht : B.Terminal) (i : B.Sorts) :
    DistribLattice (ColourEq (cloneSource B) i) :=
  CCO.RealClosure.Bounds.terminalDistribLattice
    (cloneSource B) (cloneHomogeneous B) (cloneCCO B) (B.terminal_sortNR2 ht i)

/-- The generic hierarchy's equivalence representation is literally the
actual complete source setoids, not a represented sublattice. -/
def actualEquivalenceLattice (i : B.Sorts) :
    EquivalenceLattice (ColourEq (cloneSource B) i) (CloneSAP.Carrier B.Point i) where
  relation E := E.val
  faithful := Subtype.val_injective
  inf_eq _ _ := rfl
  top_eq := rfl

def fullMIParent {i : B.Sorts} (J : FullCloneProperMI B.source i) :
    ColourEq (cloneSource B) i := miParent J.val

theorem fullMIParent_cover {i : B.Sorts} (J : FullCloneProperMI B.source i) :
    J.val ⋖ fullMIParent B J := miParent_covBy J.property.2

theorem fullMIParent_le {i : B.Sorts} (J : FullCloneProperMI B.source i)
    (L : ColourEq (cloneSource B) i) (hJL : J.val < L) : fullMIParent B J ≤ L :=
  miParent_le hJL

/-- C59: agreement of ALL actual strict coarser MI coordinates is
exactly agreement in the unique FULL parent quotient. -/
theorem fullMIKey_eq_parent_iff {i : B.Sorts} (J : FullCloneProperMI B.source i)
    (x y : Quotient J.val.val) :
    (∀ (L : ColourEq (cloneSource B) i) (hJL : J.val < L), InfIrred L →
      Quotient.map id (fun _ _ h => hJL.le h) x =
        Quotient.map id (fun _ _ h => hJL.le h) y) ↔
      Quotient.map id (fun _ _ h => (fullMIParent_cover B J).le h) x =
        Quotient.map id (fun _ _ h => (fullMIParent_cover B J).le h) y := by
  have hk := (actualEquivalenceLattice B i).key_eq_parent_iff J.val x y
  constructor
  · intro h
    apply hk.mp
    funext L
    exact h L.val L.property.1 L.property.2
  · intro h L hJL hMI
    exact congrFun (hk.mpr h) ⟨L,hJL,hMI⟩

/-- Every strict coarser MI remains a proper nonidentity named sort;
there is no missing logical-equality coordinate among these keys. -/
def strictCoarserFullMI {i : B.Sorts} (J : FullCloneProperMI B.source i)
    (L : ColourEq (cloneSource B) i) (hJL : J.val < L) (hMI : InfIrred L) :
    FullCloneProperMI B.source i :=
  ⟨L,ne_of_gt ((bot_lt_iff_ne_bot.mpr J.property.1).trans hJL),hMI⟩

theorem fullMIParent_top_no_strict_coarser {i : B.Sorts}
    (J : FullCloneProperMI B.source i) (hp : fullMIParent B J = ⊤)
    (L : ColourEq (cloneSource B) i) (hJL : J.val < L) : ¬ InfIrred L := by
  intro hMI
  have ht : L = ⊤ := top_unique (hp ▸ fullMIParent_le B J L hJL)
  exact hMI.ne_top ht

/-- C59 Top boundary: the parent quotient has only one possible value,
even though the actual J sort and its independent task may be nonempty. -/
theorem fullMIParent_top_key_constant {i : B.Sorts}
    (J : FullCloneProperMI B.source i) (hp : fullMIParent B J = ⊤)
    (x y : Quotient J.val.val) :
    Quotient.map id (fun _ _ h => (fullMIParent_cover B J).le h) x =
      Quotient.map id (fun _ _ h => (fullMIParent_cover B J).le h) y := by
  apply (fullMIKey_eq_parent_iff B J x y).mp
  intro L hJL hMI
  exact False.elim (fullMIParent_top_no_strict_coarser B J hp L hJL hMI)

end
end CCO.UnfilteredEP
