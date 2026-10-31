import CCO.RawExact.QuotientExpansionDiagram
import CCO.StrongExact.ProfileSemantics
import CCO.TerminalLattice.PositiveBranchCycles

/-!
# B050 C27: finite private diagram of optional genuine OLD positive words

The accepted B002 quotient-path expansion builds a literal finite
old-source partial atomic diagram out of independently private reduced
RAW paths. This file instantiates it at ONE ORIGINAL sort with at most
one real positive atomic word per marked pair and NO marked edge when
its optional word is absent. An absent edge is an empty presentation
(typed Top), not a fictitious original identity or an empty atom.

The source C27 whole-cycle classification remains a separate obligation.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- ONE word or no specified edges for each ordered canonical pair of
distinct marked vertices, all attached to the SAME original sort i.
The actual positive words may pass through other named old sorts. -/
def oldOptionalPositivePresentations {i : ι} {n : Nat}
    (words : CCO.RawExact.QuotientExpansion.Edge n →
      Option (PositiveWord S i i)) :
    CCO.RawExact.QuotientExpansion.Menus S (fun _ : Fin n => i) :=
  fun e => match words e with
    | none => []
    | some w => [PositiveWord.toRawWord S w]

/-- Each singleton positive-word relation is ACTUALLY nonempty under
original homogeneous SAP, via its proved STRONG profile semantics.
Every omitted edge has exactly the TRUE typed Top relation, inhabited
by the original nonempty sort. No CCO or quotient action is used. -/
theorem oldOptionalPositivePresentations_nonempty
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {n : Nat}
    (words : CCO.RawExact.QuotientExpansion.Edge n →
      Option (PositiveWord S i i)) :
    ∀ e, TRel.Nonempty
      (CCO.RawExact.evaluate S
        (oldOptionalPositivePresentations S words e)) := by
  intro e
  cases hword : words e with
  | none =>
      obtain ⟨x⟩ := S.nonemptySort i
      exact ⟨x,x,by
        intro raw hmem
        simp [oldOptionalPositivePresentations,hword] at hmem⟩
  | some w =>
      obtain ⟨a, ha⟩ := PositiveWord.profile_nonempty_of_SAP S H sap w
      obtain ⟨x,y,hxy,_⟩ :=
        (StrongExact.positive_profile_iff_represented S H sap w a).mp ha
      refine ⟨x,y,?_⟩
      intro raw hmem
      have hraw : raw = PositiveWord.toRawWord S w := by
        simpa [oldOptionalPositivePresentations,hword] using hmem
      subst raw
      rw [← PositiveWord.represented_toRawWord S w]
      exact hxy

/-- A canonical honest finite OLD partial diagram: marked roots, one
fresh private interior for every REAL diversity position of each
specified original word, and no edges between unrelated interiors.
This delegates all overlap/colour functionality to the ACCEPTED B002
private expansion rather than supplying any new edge-selection axiom. -/
noncomputable def oldOptionalPositiveDiagram
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {n : Nat}
    (words : CCO.RawExact.QuotientExpansion.Edge n →
      Option (PositiveWord S i i)) :
    PartialDiagram S
      (CCO.RawExact.QuotientExpansion.Vertex S (fun _ : Fin n => i)
        (oldOptionalPositivePresentations S words)) :=
  CCO.RawExact.QuotientExpansion.diagram S
    (fun _ : Fin n => i) (oldOptionalPositivePresentations S words)
    (oldOptionalPositivePresentations_nonempty S H sap words)

end CCO.TerminalLattice
