import CCO.AutomaticEPCore.SourceCore

/-! Final B063 source-facing core API. The caller supplies precisely the
FULL-cover terminality from A03. The equivalence with absence of every
finite strict FULL interval is proved, rather than imposed as a stronger
source hypothesis. All binary names remain ORIGINAL atom names; the
language does not acquire a predicate naming each terminal label. -/

universe u v w t
namespace CCO.AutomaticEPCore
open CCO.APCharacter CCO.APCharacter.Towers CCO.ExactEPGeometry
open CCO.ParityHasse.Original
noncomputable section

/-- The source's FULL-cover terminality is exactly the obstruction-free
terminality of the proved source/tower infrastructure. Top covers and
finite current sources are included on both sides. -/
theorem actual_terminal_iff_full_cover
    (B : CurrentSource.{u,v,w,t}) :
    B.Terminal ↔ ∀ p : B.Sorts, FullCoverTerminal B.source p := by
  constructor
  · exact actual_terminal_full_cover B
  · intro full obstruction
    obtain ⟨p,E,F,x,strict,finite⟩ := obstruction
    exact (not_finite_iff_infinite.mpr
      (terminal_full_interval_infinite B.source (full p) E F strict x)) finite

/-- The old-atom graph obtained by joining labels that share ANY
globally loopless original atom is exactly the complete irreflexive
graph. The forward implication is witnessed by an ORIGINAL bipartite
atom; the reverse implication uses literal looplessness only. -/
theorem actual_terminal_loopless_old_atom_graph_complete
    (A : CurrentSource.{u,v,w,t}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i)
    {next : CertifiedGateTower.ExactPrefix A}
    (history : History IsoGateTower.Step (CertifiedGateTower.initial A) next)
    (terminal : ∀ p : next.current.Sorts, FullCoverTerminal next.current.source p)
    (s t : next.current.Sorts) :
    s ≠ t ↔ ∃ a : A.source.Atom base base,
      (∀ q : next.current.Sorts,
        ¬originalAtomTable A next.current next.reduct base hOne a q q) ∧
      originalAtomTable A next.current next.reduct base hOne a s t := by
  constructor
  · intro different
    obtain ⟨a,bipartite,pair⟩ :=
      (actual_tower_separation A base hOne) next history
        ((actual_terminal_iff_full_cover next.current).mpr terminal) s t different
    exact ⟨a,original_bipartite_table_loopless A next.current next.reduct
      base hOne terminal a bipartite,pair⟩
  · rintro ⟨a,loopless,pair⟩ equal
    subst t
    exact loopless s pair

/-- Literal `End(T)=Aut(T)` for the same unfiltered ORIGINAL-atom table.
The finite-table inverse reflects every old atom; preservation alone is
not confused with an arbitrary infinite bijective endomorphism. -/
theorem actual_terminal_old_atom_end_iff_auto
    (A : CurrentSource.{u,v,w,t}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i)
    {next : CertifiedGateTower.ExactPrefix A}
    (history : History IsoGateTower.Step (CertifiedGateTower.initial A) next)
    (terminal : ∀ p : next.current.Sorts, FullCoverTerminal next.current.source p)
    (f : next.current.Sorts → next.current.Sorts) :
    TableEndomorphism
      (fun a s t => originalAtomTable A next.current next.reduct base hOne a s t) f ↔
    TableAutomorphism
      (fun a s t => originalAtomTable A next.current next.reduct base hOne a s t) f := by
  constructor
  · exact actual_terminal_old_atom_table_core A base hOne history
      ((actual_terminal_iff_full_cover next.current).mpr terminal) f
  · intro automorphism a s t pair
    exact (automorphism.2 a s t).mpr pair

/-- `thm:ep-automatic-core` with all three conclusions at the exact
source scope: globally loopless original bipartite atoms, complete
original bipartite separation, and every table endomorphism an
automorphism. The quotient/rank and same-F providers are discharged by
the actual source proofs, with no SAP/EP/Ramsey premise added. -/
theorem automatic_terminal_old_atom_core
    (A : CurrentSource.{u,v,w,t}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i)
    {next : CertifiedGateTower.ExactPrefix A}
    (history : History IsoGateTower.Step (CertifiedGateTower.initial A) next)
    (terminal : ∀ p : next.current.Sorts, FullCoverTerminal next.current.source p) :
    (∀ a : A.source.Atom base base, (atomGraph A.source a).IsBipartite →
      ∀ s : next.current.Sorts,
        ¬originalAtomTable A next.current next.reduct base hOne a s s) ∧
    (∀ s t : next.current.Sorts, s ≠ t →
      ∃ a : A.source.Atom base base, (atomGraph A.source a).IsBipartite ∧
        originalAtomTable A next.current next.reduct base hOne a s t) ∧
    (∀ f : next.current.Sorts → next.current.Sorts,
      TableEndomorphism
        (fun a s t => originalAtomTable A next.current next.reduct base hOne a s t) f ↔
      TableAutomorphism
        (fun a s t => originalAtomTable A next.current next.reduct base hOne a s t) f) := by
  refine ⟨?_,?_,?_⟩
  · intro a bipartite
    exact original_bipartite_table_loopless A next.current next.reduct
      base hOne terminal a bipartite
  · exact (actual_tower_separation A base hOne) next history
      ((actual_terminal_iff_full_cover next.current).mpr terminal)
  · exact actual_terminal_old_atom_end_iff_auto A base hOne history terminal

end
end CCO.AutomaticEPCore
