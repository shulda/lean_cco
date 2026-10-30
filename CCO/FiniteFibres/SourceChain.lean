import CCO.FiniteFibres.AtomicAut
import CCO.FiniteFibres.Group.FiniteCover
import CCO.FiniteFibres.Real.PaletteChain

/-! The actual finite source chain is CHOSEN and PROVED saturated, its
index-two counts telescope, and actual named colours bound its length.
The source export never requests a supplied chain or a size oracle. -/
universe u v t
namespace CCO.FiniteFibres
open Group.Correspondence

variable {A : Type u} (S : AtomicSource.{0,u,v} Unit (fun _ => A)) [Finite A]

noncomputable def sourceSaturatedChain :
    Group.SaturatedChain (⊥ : InvEq (Real.Aut S) A) ⊤ := Group.invariantSaturatedChain

noncomputable def sourceColourChain : Real.InvariantChain S (sourceSaturatedChain S).length where
  equivalence := fun i => ((sourceSaturatedChain S).point i).val
  invariant := fun i => ((sourceSaturatedChain S).point i).property
  monotone := (sourceSaturatedChain S).monotone
  strict := fun i => ((sourceSaturatedChain S).covers i).lt

variable {G : Type t} [Group G] [MulAction G A] (H : HomogeneousSource S G)
include H

/-- C32--C35: the REAL saturated full-invariant chain gives the stated
power-of-two size and consumes a DIFFERENT original colour at every step. -/
theorem actual_source_chain_bounds (cco : CCO.SemanticCCO.{0,u,0,v} S) :
    Nat.card A = 2^(sourceSaturatedChain S).length ∧
      (sourceSaturatedChain S).length ≤ Nat.card (S.Atom () ()) := by
  classical
  letI : Fintype A := Fintype.ofFinite _
  obtain ⟨n,hn⟩ := source_fullAut_two_group S cco
  have trans : ∀ x y : A, ∃ g : Real.Aut S, g • x = y :=
    S.original_sort_transitive_of_homogeneous (Real.fullHomogeneous S H) ()
  let a : A := Classical.choice (S.nonemptySort ())
  exact ⟨Group.chain_card_two_power hn trans a _,(sourceColourChain S).length_le_palette H⟩

end CCO.FiniteFibres
