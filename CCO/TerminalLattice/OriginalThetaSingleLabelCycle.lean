import CCO.TerminalLattice.OriginalThetaPresentations
import CCO.RawExact.QuotientExpansionCycleCases
import CCO.RawExact.QuotientExpansionCycleRealization

/-!
# B050 source08 C26: real old homomorphisms of two-root theta cycles

Accepted B002 proves that an old private-path simple cycle either has
only one used marked pair, or admits an injective marked cyclic projection.
In the one-pair case the existing ACTUAL endpoint witness for the complete
list of private words already realizes every cycle edge: independent
private interiors can be taken from the B002 word-path realization.
No extra CCO hypothesis, exact profile, quotient source, or artificial
identity edge is needed.

The remaining multi-mark case still requires the old assigned-menu
cycle valuation from the genuine sparse graph/star geometry.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

/-- A private-path old cycle using only ONE genuine canonical marked
edge is homomorphic in the original source. The fixed pair of OLD
real endpoints witnesses the ENTIRE specified finite family for that
edge, not just one chosen positive word or one fine menu factor. -/
theorem original_private_single_label_cycleHom
    {i : ι} {n : Nat}
    (P : CCO.RawExact.QuotientExpansion.Menus S
      (fun _ : Fin n => i))
    (hNE : ∀ e, TRel.Nonempty (CCO.RawExact.evaluate S (P e)))
    (C : SimpleCycle
      (CCO.RawExact.QuotientExpansion.diagram
        S (fun _ : Fin n => i) P hNE))
    (hPositive : ∀ o : CCO.RawExact.QuotientExpansion.Occurrence
        S (fun _ : Fin n => i) P,
        0 < CCO.RawExact.diversityLength S
          (CCO.RawExact.QuotientExpansion.word
            S (fun _ : Fin n => i) P o))
    (e : CCO.RawExact.QuotientExpansion.Edge n)
    (hAll : ∀ f,
      CCO.RawExact.CyclicSuppression.LabelOn
        (CCO.RawExact.QuotientExpansion.initialCycle
          S (fun _ : Fin n => i) P hNE C) f → f = e) :
    CycleHom C := by
  classical
  obtain ⟨x, y, hEval⟩ := hNE e
  let b : Fin n → X i := fun m =>
    if m = CCO.RawExact.QuotientExpansion.left e then x
    else if m = CCO.RawExact.QuotientExpansion.right e then y
    else Classical.choice (S.nonemptySort i)
  have hbLeft : b (CCO.RawExact.QuotientExpansion.left e) = x := by
    simp [b]
  have hbRight : b (CCO.RawExact.QuotientExpansion.right e) = y := by
    simp [b, (CCO.RawExact.QuotientExpansion.left_ne_right e).symm]
  apply CCO.RawExact.QuotientExpansion.cycleHom_of_marked_edge_realization
    S (fun _ : Fin n => i) P hNE C b
  · intro f hUsed
    obtain ⟨k, o, p, q, hpq, hv, hw, hf⟩ := hUsed
    have hLabel :
        CCO.RawExact.CyclicSuppression.LabelOn
          (CCO.RawExact.QuotientExpansion.initialCycle
            S (fun _ : Fin n => i) P hNE C) f := by
      refine ⟨k, ?_⟩
      exact (CCO.RawExact.QuotientExpansion.initial_label_of_path_witness
        S (fun _ : Fin n => i) P hNE C k o p q hpq hv hw).trans hf
    have hfe : f = e := hAll f hLabel
    have hActualEdge : o.1 = e := hf.trans hfe
    simpa only [hActualEdge, hbLeft, hbRight] using hEval
  · exact hPositive

/-- Concrete C26 source branch decomposition for the REAL original
multi-theta network. Every simple cycle either already has a FULL
original old colour-preserving homomorphism, or has a true B002
marked projection of length at least three, with all used edges.

This is a genuine case reduction: it does NOT assert that the still
open projected cyclic root valuation automatically exists. -/
theorem originalTheta_cycleHom_or_marked_projection
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {n : Nat}
    (families : CCO.RawExact.QuotientExpansion.Edge n →
      List (PositiveWord S i i))
    (guards : CCO.RawExact.QuotientExpansion.Edge n → S.Menu i i)
    (hGuard : ∀ e, families e ≠ [] →
      (guards e).Nonempty ∧
      ∀ p ∈ families e, guards e ⊆ PositiveWord.profile S p)
    (C : SimpleCycle
      (originalThetaDiagram S H sap families guards hGuard)) :
    CycleHom C ∨
      Nonempty (CCO.RawExact.QuotientExpansion.MarkedProjection
        S (fun _ : Fin n => i)
        (originalThetaPresentations S families)
        (originalThetaPresentations_nonempty S H sap families guards hGuard)
        C) := by
  let P := originalThetaPresentations S families
  let hNE := originalThetaPresentations_nonempty
    S H sap families guards hGuard
  rcases CCO.RawExact.QuotientExpansion.cycle_marked_cases
      S (fun _ : Fin n => i) P hNE C with hOne | hMany
  · left
    obtain ⟨e, _he, _hMarks, hAll⟩ := hOne
    exact original_private_single_label_cycleHom S P hNE C
      (originalThetaPresentations_occurrence_positive S families)
      e hAll
  · exact Or.inr hMany

end CCO.TerminalLattice
