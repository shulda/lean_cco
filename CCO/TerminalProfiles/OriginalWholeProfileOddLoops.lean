import CCO.TerminalProfiles.OriginalOddLoopStabilization
import CCO.TerminalPowers.GraphSource
import CCO.RealClosure.Bounds.TerminalNR2
import CCO.PositiveWords

/-! B051 TWP: original NR2 supplies real odd walks of the WHOLE word relation. -/

universe u v w t

namespace CCO.TerminalProfiles

open CCO.ParityHasse.Original

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

private theorem relPow_of_pointwise_relation
    {A : Type v} {P R : A → A → Prop}
    (hPR : ∀ x y, P x y → R x y) :
    ∀ n x y, relPow P n x y → relPow R n x y := by
  intro n
  induction n with
  | zero =>
      intro x y h
      exact h
  | succ n ih =>
      intro x y h
      obtain ⟨z,hxz,hzy⟩ := h
      exact ⟨z,hPR x z hxz,ih z y hzy⟩

/-- Real original whole-word RAW powers stabilize to connectedness. -/
theorem original_whole_positive_word_raw_eventually_connected
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : CCO.Selectors.OriginalNR2 S)
    {i : ι} (word : PositiveWord S i i) :
    ∃ N : Nat, 0 < N ∧ ∀ n, N ≤ n →
      relPow (PositiveWord.represented S word) n =
        (fun x y => ∃ k : Nat,
          relPow (PositiveWord.represented S word) k x y) := by
  classical
  let R : X i → X i → Prop := PositiveWord.represented S word
  have hInvariant : TRel.Invariant (G := G) R :=
    PositiveWord.represented_invariant_of_homogeneous S H word
  have hColour : ColourInvariant S i R :=
    groupInvariant_colourInvariant S H hInvariant
  have hSymm : ∀ x y, R x y → R y x :=
    colourInvariant_symmetric S hColour
  obtain ⟨atom,hAtomW⟩ := PositiveWord.profile_nonempty_of_SAP S H sap word
  have hAllAtom : ∀ x y : X i, S.atomRel atom x y → R x y := by
    intro x y hcol
    have hGuard : S.diversityGuard R = PositiveWord.profile S word :=
      PositiveWord.diversityGuard_represented_eq_profile_of_SAP S H sap word
    have hIn : atom ∈ S.diversityGuard R := by
      rw [hGuard]
      exact hAtomW
    obtain ⟨a,b,hRab,hcolab⟩ := hIn
    exact (hColour a b x y (hcolab.trans hcol.symm)).mp hRab
  have hSerial : ∀ x : X i, ∃ y, R x y := by
    obtain ⟨a,b,hab⟩ := S.realized atom
    exact invariant_nonempty_serial S H hColour
      ⟨a,b,hAllAtom a b hab⟩
  have hSortNR2 : CCO.RealClosure.Bounds.SortNR2 S i :=
    CCO.RealClosure.Bounds.sortNR2_of_originalNR2 S H nr2
  have hOdd : ∀ x : X i, ∃ m : Nat, Odd m ∧ relPow R m x x := by
    intro x
    obtain ⟨p,hpOdd⟩ :=
      CCO.TerminalPowers.nr2_odd_walk S H hSortNR2 atom x
    have hAtomWalk : relPow (S.atomRel atom) p.length x x :=
      (relPow_atom_iff_walk S atom p.length x x).mpr ⟨p,rfl⟩
    exact ⟨p.length,hpOdd,
      relPow_of_pointwise_relation hAllAtom p.length x x hAtomWalk⟩
  exact original_odd_loop_raw_powers_eventually_connected
    S H R hColour hSymm hSerial hOdd

end CCO.TerminalProfiles
