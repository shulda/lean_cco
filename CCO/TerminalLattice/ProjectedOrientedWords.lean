import CCO.TerminalLattice.ProjectedCycleRootValues
import CCO.TerminalLattice.SparseCycleProjectionEdges
import CCO.TerminalLattice.ReversePositiveWord

/-!
# B050 C27: canonical ORIGINAL positive word in cyclic marked orientation

The exact B002 marked projection, and the one-word-per-pair PRIVATE OLD
network, force a REAL selected positive word for every used marked pair.
For a reversed cyclic traversal we use the genuine converse of the entire
OLD typed positive word, not an invented symmetric word or a permutation
of its internal old named-sort letters.

This module makes the final root-valuation-to-CycleHom bridge canonical:
one ordered cyclic relation for each actually traversed positive branch
is enough. It neither assumes any raw cycle map nor supplies the
still-open source-specific saturated graph/spoke branch spectrum.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

/-- Every literal compressed marked edge of ONE actual optional-positive
source diagram has a REAL positive original word selected on its
canonical pair. This holds even for direct words of length one. -/
theorem oldOptionalPositive_projected_word_exists
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {n : Nat}
    (words : CCO.RawExact.QuotientExpansion.Edge n →
      Option (PositiveWord S i i))
    (C : SimpleCycle (oldOptionalPositiveDiagram S H sap words))
    (B : CCO.RawExact.QuotientExpansion.MarkedProjection
      S (fun _ : Fin n => i)
      (oldOptionalPositivePresentations S words)
      (oldOptionalPositivePresentations_nonempty S H sap words) C)
    (k : Fin B.length) :
    ∃ word : PositiveWord S i i, words (B.edges k) = some word := by
  have hUsed : CCO.RawExact.CyclicSuppression.LabelOn
      (CCO.RawExact.QuotientExpansion.initialCycle S
        (fun _ : Fin n => i)
        (oldOptionalPositivePresentations S words)
        (oldOptionalPositivePresentations_nonempty S H sap words) C)
      (B.edges k) :=
    (B.labels_iff (B.edges k)).mpr ⟨k,rfl⟩
  exact oldOptionalPositive_used_marked_edge_has_word
    S H sap words C (B.edges k) hUsed

/-- The actual canonical OLD positive word of a used marked pair,
chosen only from its proven singleton presentation. -/
noncomputable def oldProjectedCanonicalWord
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {n : Nat}
    (words : CCO.RawExact.QuotientExpansion.Edge n →
      Option (PositiveWord S i i))
    (C : SimpleCycle (oldOptionalPositiveDiagram S H sap words))
    (B : CCO.RawExact.QuotientExpansion.MarkedProjection
      S (fun _ : Fin n => i)
      (oldOptionalPositivePresentations S words)
      (oldOptionalPositivePresentations_nonempty S H sap words) C)
    (k : Fin B.length) : PositiveWord S i i :=
  Classical.choose
    (oldOptionalPositive_projected_word_exists S H sap words C B k)

/-- The canonical positive word really is the ONLY selected word on
this used marked pair; no unlisted/absent graph edge is introduced. -/
theorem oldProjectedCanonicalWord_selected
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {n : Nat}
    (words : CCO.RawExact.QuotientExpansion.Edge n →
      Option (PositiveWord S i i))
    (C : SimpleCycle (oldOptionalPositiveDiagram S H sap words))
    (B : CCO.RawExact.QuotientExpansion.MarkedProjection
      S (fun _ : Fin n => i)
      (oldOptionalPositivePresentations S words)
      (oldOptionalPositivePresentations_nonempty S H sap words) C)
    (k : Fin B.length) :
    words (B.edges k) =
      some (oldProjectedCanonicalWord S H sap words C B k) :=
  Classical.choose_spec
    (oldOptionalPositive_projected_word_exists S H sap words C B k)

/-- The word for a projected edge IN ITS ACTUAL CYCLIC TRAVERSAL
orientation: either the genuine original canonical positive word,
or its OLD typed reversal (with real converse atoms). -/
noncomputable def oldProjectedOrientedWord
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {n : Nat}
    (words : CCO.RawExact.QuotientExpansion.Edge n →
      Option (PositiveWord S i i))
    (C : SimpleCycle (oldOptionalPositiveDiagram S H sap words))
    (B : CCO.RawExact.QuotientExpansion.MarkedProjection
      S (fun _ : Fin n => i)
      (oldOptionalPositivePresentations S words)
      (oldOptionalPositivePresentations_nonempty S H sap words) C)
    (k : Fin B.length) : PositiveWord S i i :=
  if B.vertices k =
      CCO.RawExact.QuotientExpansion.left (B.edges k) then
    oldProjectedCanonicalWord S H sap words C B k
  else
    originalPositiveWordReverse S
      (oldProjectedCanonicalWord S H sap words C B k)

/-- Original source symmetry/SAP make a whole same-sort STRONG word
profile invariant under reversing the ACTUAL typed word. This does not
allow commuting its internal old letters: only its endpoint menu is
orientation-independent. -/
theorem oldProjectedOrientedWord_profile
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {n : Nat}
    (words : CCO.RawExact.QuotientExpansion.Edge n →
      Option (PositiveWord S i i))
    (C : SimpleCycle (oldOptionalPositiveDiagram S H sap words))
    (B : CCO.RawExact.QuotientExpansion.MarkedProjection
      S (fun _ : Fin n => i)
      (oldOptionalPositivePresentations S words)
      (oldOptionalPositivePresentations_nonempty S H sap words) C)
    (k : Fin B.length) :
    PositiveWord.profile S (oldProjectedOrientedWord S H sap words C B k) =
      PositiveWord.profile S (oldProjectedCanonicalWord S H sap words C B k) := by
  unfold oldProjectedOrientedWord
  split_ifs
  · rfl
  · exact originalPositiveWordReverse_same_sort_profile
      S H sap (oldProjectedCanonicalWord S H sap words C B k)

/-- The exact B002 receiving theorem, with the orientation condition
now supplied by the canonically chosen positive word for each ACTUAL
used edge rather than by a separate per-edge existential assumption.
If ALL these ordered old relations hold for ONE common finite cyclic
root valuation, the entire raw CYCLE has an actual source homomorphism
including every private typed interior.

The existence of this common valuation remains to be derived from
the independently proved C29/C30 source graph/spoke spectra. -/
theorem oldOptionalPositive_cycleHom_of_oriented_values
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {n : Nat}
    (words : CCO.RawExact.QuotientExpansion.Edge n →
      Option (PositiveWord S i i))
    (C : SimpleCycle (oldOptionalPositiveDiagram S H sap words))
    (B : CCO.RawExact.QuotientExpansion.MarkedProjection
      S (fun _ : Fin n => i)
      (oldOptionalPositivePresentations S words)
      (oldOptionalPositivePresentations_nonempty S H sap words) C)
    (values : Fin B.length → X i)
    (hWords : ∀ k : Fin B.length,
      PositiveWord.represented S
        (oldProjectedOrientedWord S H sap words C B k)
        (values k) (values (CCO.cyclicNext B.length_pos k))) :
    CycleHom C := by
  apply oldOptionalPositive_cycleHom_of_projected_root_values
    S H sap words C B values
  intro k
  let word := oldProjectedCanonicalWord S H sap words C B k
  refine ⟨word, oldProjectedCanonicalWord_selected S H sap words C B k, ?_, ?_⟩
  · intro hForward
    have hActual :
        oldProjectedOrientedWord S H sap words C B k = word := by
      simp [oldProjectedOrientedWord,hForward,word]
    simpa only [hActual] using hWords k
  · intro hBackward
    have hNotLeft : B.vertices k ≠
        CCO.RawExact.QuotientExpansion.left (B.edges k) := by
      intro hLeft
      exact CCO.RawExact.QuotientExpansion.left_ne_right (B.edges k)
        (hLeft.symm.trans hBackward)
    have hActual :
        oldProjectedOrientedWord S H sap words C B k =
          originalPositiveWordReverse S word := by
      simp [oldProjectedOrientedWord,hNotLeft,word]
    have hRel := hWords k
    rw [hActual, originalPositiveWordReverse_represented S word] at hRel
    exact hRel

end CCO.TerminalLattice
