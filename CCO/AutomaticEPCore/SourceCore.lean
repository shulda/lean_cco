import CCO.AutomaticEPCore.OriginalRankInduction
import CCO.AutomaticEPCore.FiniteCore
import CCO.AutomaticEPCore.SourceLoopless

/-! The finite terminal original-atom table is a genuine core.
The source remains one-sort AP+HOM-CCO, with finite and non-SAP quotient
cases already handled by the proved strong ORIGINAL-rank induction.
No new unary singleton labels are introduced into the table language. -/

universe u v w t
namespace CCO.AutomaticEPCore
open CCO.APCharacter CCO.APCharacter.Towers CCO.ExactEPGeometry
open CCO.ParityHasse.Original
noncomputable section

/-- True terminal obstruction-freeness implies no finite relative class
at EVERY strict FULL invariant-equivalence cover, including Top covers. -/
theorem actual_terminal_full_cover
    (B : CurrentSource.{u,v,w,t}) (terminal : B.Terminal) :
    ∀ p : B.Sorts, FullCoverTerminal B.source p := by
  intro p E F hCover x
  apply (not_finite_iff_infinite).mp
  intro hFinite
  exact terminal ⟨p,E,F,x,hCover.lt,hFinite⟩

/-- Actual one-sort original old-atom table after a genuine terminal
maximal-character tower. Every endomorphism of the finite table
preserving ONLY the old atom predicates is an automorphism (preservation
AND reflection), without individually naming any of the new labels. -/
theorem actual_terminal_old_atom_table_core
    (A : CurrentSource.{u,v,w,t}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i)
    {next : CertifiedGateTower.ExactPrefix A}
    (history : History IsoGateTower.Step (CertifiedGateTower.initial A) next)
    (terminal : next.current.Terminal)
    (f : next.current.Sorts → next.current.Sorts)
    (hf : TableEndomorphism
      (fun a s t => originalAtomTable A next.current next.reduct base hOne a s t) f) :
    TableAutomorphism
      (fun a s t => originalAtomTable A next.current next.reduct base hOne a s t) f := by
  classical
  letI : Fintype next.current.Sorts := next.current.source.finiteSort
  let R : A.source.Atom base base → next.current.Sorts → next.current.Sorts → Prop :=
    originalAtomTable A next.current next.reduct base hOne
  let BP : Set (A.source.Atom base base) :=
    {a | (atomGraph A.source a).IsBipartite}
  have hFull := actual_terminal_full_cover next.current terminal
  have hLoopless : ∀ a ∈ BP, ∀ s, ¬R a s s := by
    intro a ha s
    exact original_bipartite_table_loopless A next.current next.reduct base
      hOne hFull a ha s
  have hSeparates : ∀ s t : next.current.Sorts, s ≠ t →
      ∃ a ∈ BP, R a s t := by
    intro s t hst
    obtain ⟨a,hBP,ha⟩ :=
      (actual_tower_separation A base hOne) next history terminal s t hst
    exact ⟨a,hBP,ha⟩
  exact finite_table_core_of_separation R BP hLoopless hSeparates f hf

end
end CCO.AutomaticEPCore
