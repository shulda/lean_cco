import CCO.TerminalLattice.SparseCycleUsedWords
import CCO.TerminalLattice.OptionalPositiveReadout

/-!
# B050 C27: from genuinely ordered projected-branch root values to a cycle map

The accepted B002 marked projection already remembers EVERY actually
traversed labelled old edge. This file proves that fact for the
literal CCO `CycleUsesEdge` predicate and extends an actual finite
cyclic list of OLD marked-root values to all original marked names.
An orientation-aware relation for each selected private OLD word
then constructs a homomorphism of the COMPLETE original raw cycle
using the accepted B002 finite-private-path constructor.

The premise is actual real OLD values satisfying the specifically
ordered represented positive words. It is not an assumed cycle map,
and obtaining those values from the C29/C30 sparse graph spectra for
ALL projected cycles remains the source C27 combinatorial task.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

/-- Extend old real values on an injectively enumerated finite set
of marked indices to EVERY marked index, without changing their
specified values or identifying source labels. Off the actual
projection, choose any actual old source point of the same sort. -/
noncomputable def oldMarkedProjectionExtend
    {i : ι} {m n : Nat}
    (f : Fin m ↪ Fin n) (values : Fin m → X i) :
    Fin n → X i :=
  fun root =>
    if h : ∃ k : Fin m, f k = root then
      values (Classical.choose h)
    else
      Classical.choice (S.nonemptySort i)

/-- The extension is literally the supplied old value at each genuine
marked projection vertex; the proof uses injectivity of the embedding. -/
theorem oldMarkedProjectionExtend_on
    {i : ι} {m n : Nat}
    (f : Fin m ↪ Fin n) (values : Fin m → X i)
    (k : Fin m) :
    oldMarkedProjectionExtend S f values (f k) = values k := by
  classical
  unfold oldMarkedProjectionExtend
  split_ifs with h
  · have hIndex : Classical.choose h = k :=
      f.injective (Classical.choose_spec h)
    exact congrArg values hIndex
  · exact False.elim (h ⟨k,rfl⟩)

/-- A marked pair is ACTUALLY used in a B002 raw simple cycle only if
it occurs in the compressed projection. We use B002's genuine
`initial_label_of_path_witness` to avoid assuming that the private
word occurrence chosen by `initialCycle` equals a particular witness.
All overlapping direct edges are handled by that accepted theorem. -/
theorem oldOptionalPositive_projected_covers_used_pair
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {n : Nat}
    (words : CCO.RawExact.QuotientExpansion.Edge n →
      Option (PositiveWord S i i))
    (C : SimpleCycle (oldOptionalPositiveDiagram S H sap words))
    (B : CCO.RawExact.QuotientExpansion.MarkedProjection
      S (fun _ : Fin n => i)
      (oldOptionalPositivePresentations S words)
      (oldOptionalPositivePresentations_nonempty S H sap words) C)
    (e : CCO.RawExact.QuotientExpansion.Edge n)
    (hUsed : CCO.RawExact.QuotientExpansion.CycleUsesEdge S
      (fun _ : Fin n => i)
      (oldOptionalPositivePresentations S words)
      (oldOptionalPositivePresentations_nonempty S H sap words) C e) :
    ∃ k : Fin B.length, B.edges k = e := by
  obtain ⟨k,o,p,q,hAdj,hFirst,hSecond,hEdge⟩ := hUsed
  apply (B.labels_iff e).mp
  refine ⟨k,?_⟩
  exact (CCO.RawExact.QuotientExpansion.initial_label_of_path_witness
    S (fun _ : Fin n => i)
    (oldOptionalPositivePresentations S words)
    (oldOptionalPositivePresentations_nonempty S H sap words)
    C k o p q hAdj hFirst hSecond).trans hEdge

/-- B002 receiving bridge with EXPLICIT real old source values for
each projected cyclic root. For each used canonical edge, the real
positive word must hold in the matching canonical direction. The two
implications in `hWords` impose the correct OLD orientation for
both possible cyclic traversals, without inventing reversal of atomic
letters or quotient colours.

All other marked vertices receive harmless actual old points. The
result is a literal homomorphism of the entire ORIGINAL raw simple
cycle, including every private typed intermediate vertex. -/
theorem oldOptionalPositive_cycleHom_of_projected_root_values
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
      ∃ word : PositiveWord S i i,
        words (B.edges k) = some word ∧
        (B.vertices k =
          CCO.RawExact.QuotientExpansion.left (B.edges k) →
          PositiveWord.represented S word
            (values k) (values (CCO.cyclicNext B.length_pos k))) ∧
        (B.vertices k =
          CCO.RawExact.QuotientExpansion.right (B.edges k) →
          PositiveWord.represented S word
            (values (CCO.cyclicNext B.length_pos k)) (values k))) :
    CycleHom C := by
  let b : Fin n → X i := oldMarkedProjectionExtend S B.vertices values
  have hb : ∀ k : Fin B.length, b (B.vertices k) = values k :=
    oldMarkedProjectionExtend_on S B.vertices values
  apply oldOptionalPositiveCycleHom_of_marked_values S H sap words C b
  intro e hUsed
  obtain ⟨k,hEdge⟩ :=
    oldOptionalPositive_projected_covers_used_pair S H sap words C B e hUsed
  subst e
  obtain ⟨word,hWord,hForward,hBackward⟩ := hWords k
  intro raw hRaw
  have hRawEq : raw = PositiveWord.toRawWord S word := by
    simpa [oldOptionalPositivePresentations,hWord] using hRaw
  subst raw
  rw [← PositiveWord.represented_toRawWord S word]
  rcases B.endpoints k with ⟨hFirst,hSecond⟩ | ⟨hFirst,hSecond⟩
  · rw [← hFirst, ← hSecond, hb k, hb (CCO.cyclicNext B.length_pos k)]
    exact hForward hFirst
  · rw [← hSecond, ← hFirst, hb (CCO.cyclicNext B.length_pos k), hb k]
    exact hBackward hFirst

end CCO.TerminalLattice
