import CCO.APRamseyReadout.TupleScheme
import CCO.TypedOrbitFrames.FullMIMeetPrime

/-!
# B064 C73--C74: selected MI charts are cofinal among all proper kernels

The ambient lattice is the FULL colour-invariant equivalence lattice of
one actual terminal pure-clone source. Its distributivity is derived from
semantic CCO and the actual terminal NR2 theorem, rather than postulated
for the chosen chart. The finite chart has literal meet K. Consequently
every proper named MI kernel lies above at least one selected coordinate.
-/

universe u v w p
namespace CCO.UnfilteredEP
open CCO.ParityHasse.Original CCO.CloneTupleGeometry CCO.CloneTupleGeometry.OwnerStage
open CCO.APRamseyReadout CCO.TypedOrbitFrames
noncomputable section

variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal) (F : Charts.{u,v,w,p} B)

/-- C73. Every proper named FULL MI kernel contains the actual clone
kernel, even when it does not occur in the fixed chart. -/
theorem named_kernel_contains_clone {i : B.Sorts} (D : NamedCoordinate B i) :
    fullCloneKernel B.source i ≤ D.val :=
  fullCloneKernel_le_nonidentity B.source i D.val (fullMIOfNamed B i D).property.1

/-- C73. Distributivity of the entire actual FULL lattice, including Top.
The source exact-word and distributive-lattice providers are discharged at
this same genuine terminal endpoint. -/
@[instance_reducible] def terminalFullDistribLattice (i : B.Sorts) :
    letI := ColourEq.lattice (cloneSource B) (cloneHomogeneous B) (i := i)
    DistribLattice (ColourEq (cloneSource B) i) :=
  CCO.RealClosure.Bounds.terminalDistribLattice (cloneSource B) (cloneHomogeneous B)
    (cloneCCO B) (B.terminal_sortNR2 ht i)

/-- C73. The selected finite family has its meet in the FULL lattice,
not merely among represented word-equivalences. -/
theorem selected_actual_meet (i : B.Sorts) :
    originalActualMeetEquivalence (cloneSource B)
      (fun k : Fin (chartArity F i) => (chartSymbol F i k).val) =
      fullCloneKernel B.source i := by
  apply ColourEq.ext
  intro x y
  change (∀ k : Fin (chartArity F i), (chartSymbol F i k).val x y) ↔ _
  constructor
  · intro h
    apply ((F i).meet_iff x y).mp
    intro a
    obtain ⟨k,rfl⟩ := (chartEnumeration F i).symm.surjective a
    exact h k
  · intro h k
    exact (((F i).meet_iff x y).mpr h) ((chartEnumeration F i).symm k)

include ht in
/-- C74. Every proper FULL named MI has one selected coordinate below it.
This is the genuine finite distributive meet-prime argument. In particular
no condition that the finite hidden host already contain a root is used. -/
theorem selected_coordinate_below_named {i : B.Sorts} (D : NamedCoordinate B i) :
    ∃ k : Fin (chartArity F i), (chartSymbol F i k).val ≤ D.val := by
  let J := fullMIOfNamed B i D
  apply original_terminal_full_meet_prime_coordinate
    (cloneSource B) (cloneHomogeneous B) (cloneCCO B)
    (B.terminal_sortNR2 ht i) D.val
    J.property.2.ne_top
    (fun A C hAC => J.property.2.2 hAC)
    (fun k : Fin (chartArity F i) => (chartSymbol F i k).val)
  rw [selected_actual_meet B F i]
  exact named_kernel_contains_clone B D

end
end CCO.UnfilteredEP
