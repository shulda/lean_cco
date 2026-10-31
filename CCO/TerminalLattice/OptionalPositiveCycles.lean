import CCO.TerminalLattice.OptionalPositiveNetwork
import CCO.RawExact.QuotientExpansionThetaChoices

/-!
# B050 C27: all genuine cycles meet at least THREE marked roots

Our ONE private positive word per marked pair excludes the
two-mark/two-branch theta case of the accepted B002 cycle
classification. A genuine cycle must therefore have a concrete
three-or-more-marked-vertex projection, with literal marked edge
identifiers and their actual cyclic order.

This is a real structural consequence of the constructed original
partial diagram, not an assumed projection or an application of CCO.
The projection's further reduction to a cycle of the chosen
sparse graph plus its star at the centre remains a separate step.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- A missing marked edge has zero private occurrences; a present
positive original word has precisely ONE. Both cases are exact. -/
theorem oldOptionalPositivePresentations_length_le_one
    {i : ι} {n : Nat}
    (words : CCO.RawExact.QuotientExpansion.Edge n →
      Option (PositiveWord S i i))
    (e : CCO.RawExact.QuotientExpansion.Edge n) :
    (oldOptionalPositivePresentations S words e).length ≤ 1 := by
  cases h : words e with
  | none => simp [oldOptionalPositivePresentations,h]
  | some p => simp [oldOptionalPositivePresentations,h]

/-- Actual C27 elimination of single-marked-edge simple cycles.
The accepted B002 `cycle_marked_cases` already proves that all
private interiors of a cycle belong to whole paths. If the cycle
used only one marked pair, `two_mark_choices` would yield TWO
different word occurrences on that pair; this is impossible since
our marked presentation has at most one word.

Consequently each actual cycle has a genuine finite cyclic marked
projection. No hidden CCO/conditional cycle-classification provider. -/
theorem oldOptionalPositiveDiagram_cycle_has_marked_projection
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {n : Nat}
    (words : CCO.RawExact.QuotientExpansion.Edge n →
      Option (PositiveWord S i i))
    (C : SimpleCycle (oldOptionalPositiveDiagram S H sap words)) :
    Nonempty
      (CCO.RawExact.QuotientExpansion.MarkedProjection S
        (fun _ : Fin n => i)
        (oldOptionalPositivePresentations S words)
        (oldOptionalPositivePresentations_nonempty S H sap words) C) := by
  let sort : Fin n → ι := fun _ => i
  let P := oldOptionalPositivePresentations S words
  let hNE := oldOptionalPositivePresentations_nonempty S H sap words
  rcases CCO.RawExact.QuotientExpansion.cycle_marked_cases
      S sort P hNE C with ⟨e, he, _, hAll⟩ | hProjection
  · obtain ⟨choice⟩ :=
      CCO.RawExact.QuotientExpansion.two_mark_choices
        S sort P hNE C e he hAll
    have hLength : (P e).length ≤ 1 :=
      oldOptionalPositivePresentations_length_le_one S words e
    have hFiber :
        ∀ (o₁ o₂ : CCO.RawExact.QuotientExpansion.Occurrence S sort P),
          o₁.1 = e → o₂.1 = e → o₁ = o₂ := by
      rintro ⟨f,p⟩ ⟨g,q⟩ hf hg
      change f = e at hf
      change g = e at hg
      subst f
      subst g
      have hpq : p = q := Fin.ext (by
        have hp := p.isLt
        have hq := q.isLt
        omega)
      exact congrArg
        (fun k : Fin (P e).length =>
          (⟨e,k⟩ : CCO.RawExact.QuotientExpansion.Occurrence S sort P))
        hpq
    exact False.elim
      (choice.occurrences_ne
        (hFiber choice.first choice.second
          choice.first_label choice.second_label))
  · exact hProjection

end CCO.TerminalLattice
