import CCO.TerminalLattice.OriginalThetaSingleLabelCycle
import CCO.TerminalLattice.ProjectedCycleRootValues

/-!
# B050 source08 C26–C27: genuine OLD menu-valued marked cycles

Multiple private typed OLD positive branches may share a marked pair.
Their individual STRONG spectra only CONTAIN their assigned fine menu:
we must realize a common actual OLD fine endpoint pair for ALL branches.

These lemmas transfer a real old cyclic root assignment satisfying each
assigned fine STRONG menu to a homomorphism of the ENTIRE original private
simple cycle using the accepted B002 literal expansion constructor.
They respect the actual orientation of the compressed marked cycle.

Constructing such a menu-valued assignment for every long sparse
W-graph or star cycle is still the separate source C27–C30 task.
There is no additional semantic CCO, singleton-word assumption, quotient
homogeneity, source axiom, or synthetic identity edge.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

/-- An actual same-sort fine STRONG menu is symmetric, because the
genuine OLD atomic colours are symmetric on each original sort. -/
theorem originalTheta_menuRel_symm
    {i : ι} (D : S.Menu i i) (x y : X i)
    (h : S.menuRel D x y) : S.menuRel D y x := by
  obtain ⟨a, ha, hcol⟩ := h
  have hRev : S.colour y x = some (S.conv a) :=
    (S.colour_swap x y a).mp hcol
  exact ⟨a, ha, by simpa only [S.symmetricLoop a] using hRev⟩

/-- For a genuinely used marked edge of a B002 projected cycle,
a common ORIGINAL fine menu realisation at its CANONICAL endpoint
pair satisfies ALL private positive typed OLD words on that edge.
The accepted original B002 finite-path realization then gives an
honest homomorphism of the whole specified source simple cycle.

An absent family is not used: its presentation is literally empty.
No exactness of any individual word profile is assumed. -/
theorem originalTheta_cycleHom_of_marked_canonical_guards
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {n : Nat}
    (families : CCO.RawExact.QuotientExpansion.Edge n →
      List (PositiveWord S i i))
    (guards : CCO.RawExact.QuotientExpansion.Edge n → S.Menu i i)
    (hGuard : ∀ e, families e ≠ [] →
      (guards e).Nonempty ∧
      ∀ p ∈ families e, guards e ⊆ PositiveWord.profile S p)
    (C : SimpleCycle (originalThetaDiagram S H sap families guards hGuard))
    (B : CCO.RawExact.QuotientExpansion.MarkedProjection
      S (fun _ : Fin n => i)
      (originalThetaPresentations S families)
      (originalThetaPresentations_nonempty S H sap families guards hGuard) C)
    (b : Fin n → X i)
    (hCanonical : ∀ k : Fin B.length,
      S.menuRel (guards (B.edges k))
        (b (CCO.RawExact.QuotientExpansion.left (B.edges k)))
        (b (CCO.RawExact.QuotientExpansion.right (B.edges k)))) :
    CycleHom C := by
  let P := originalThetaPresentations S families
  let hNE := originalThetaPresentations_nonempty S H sap families guards hGuard
  apply CCO.RawExact.QuotientExpansion.cycleHom_of_marked_edge_realization
    S (fun _ : Fin n => i) P hNE C b
  · intro e hUsed
    obtain ⟨k, o, p, q, hpq, hv, hw, hEdge⟩ := hUsed
    have hLabel :
        CCO.RawExact.CyclicSuppression.LabelOn
          (CCO.RawExact.QuotientExpansion.initialCycle
            S (fun _ : Fin n => i) P hNE C) e := by
      refine ⟨k, ?_⟩
      exact (CCO.RawExact.QuotientExpansion.initial_label_of_path_witness
        S (fun _ : Fin n => i) P hNE C k o p q hpq hv hw).trans hEdge
    obtain ⟨edgeIndex, hSame⟩ := (B.labels_iff e).mp hLabel
    have hMenu : S.menuRel (guards e)
        (b (CCO.RawExact.QuotientExpansion.left e))
        (b (CCO.RawExact.QuotientExpansion.right e)) := by
      rw [← hSame]
      exact hCanonical edgeIndex
    intro raw hRaw
    have hMem :
        raw ∈ (families e).map (PositiveWord.toRawWord S) := by
      simpa only [P, originalThetaPresentations] using hRaw
    obtain ⟨pword, hpword, hRawEq⟩ := List.mem_map.mp hMem
    have hPresent : families e ≠ [] := by
      intro hEmpty
      simp [hEmpty] at hpword
    have hSub : guards e ⊆ PositiveWord.profile S pword :=
      (hGuard e hPresent).2 pword hpword
    rw [← hRawEq, ← PositiveWord.represented_toRawWord S pword]
    exact originalPositiveWord_represented_of_menuRel
      S H sap (guards e) pword hSub _ _ hMenu
  · exact originalThetaPresentations_occurrence_positive S families

/-- Actual cyclic-order C27 receiver: one real OLD value per distinct
marked root, satisfying the true assigned SAME-SORT fine menu for
every consecutive projected edge, is sufficient for a homomorphism of
the full original private simple cycle, including all typed interiors.

The B002 endpoint alternatives and OLD symmetry handle reversed
traversals WITHOUT reversing individual atomic word letters. -/
theorem originalTheta_cycleHom_of_projected_guard_values
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {n : Nat}
    (families : CCO.RawExact.QuotientExpansion.Edge n →
      List (PositiveWord S i i))
    (guards : CCO.RawExact.QuotientExpansion.Edge n → S.Menu i i)
    (hGuard : ∀ e, families e ≠ [] →
      (guards e).Nonempty ∧
      ∀ p ∈ families e, guards e ⊆ PositiveWord.profile S p)
    (C : SimpleCycle (originalThetaDiagram S H sap families guards hGuard))
    (B : CCO.RawExact.QuotientExpansion.MarkedProjection
      S (fun _ : Fin n => i)
      (originalThetaPresentations S families)
      (originalThetaPresentations_nonempty S H sap families guards hGuard) C)
    (values : Fin B.length → X i)
    (hCycle : ∀ k : Fin B.length,
      S.menuRel (guards (B.edges k))
        (values k) (values (CCO.cyclicNext B.length_pos k))) :
    CycleHom C := by
  let b : Fin n → X i :=
    oldMarkedProjectionExtend S B.vertices values
  have hb : ∀ k : Fin B.length,
      b (B.vertices k) = values k :=
    oldMarkedProjectionExtend_on S B.vertices values
  apply originalTheta_cycleHom_of_marked_canonical_guards
    S H sap families guards hGuard C B b
  intro k
  rcases B.endpoints k with ⟨hFirst,hSecond⟩ | ⟨hFirst,hSecond⟩
  · rw [← hFirst, ← hSecond, hb k, hb (CCO.cyclicNext B.length_pos k)]
    exact hCycle k
  · rw [← hSecond, ← hFirst, hb (CCO.cyclicNext B.length_pos k), hb k]
    exact originalTheta_menuRel_symm S (guards (B.edges k))
      (values k) (values (CCO.cyclicNext B.length_pos k)) (hCycle k)

end CCO.TerminalLattice
