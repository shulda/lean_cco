import CCO.Selectors.PriorityTie
import Mathlib.Data.Prod.Lex
import Mathlib.Order.Basic

/-!
# A genuine converse-compatible total order realizing terminal global gates

The first key coordinate reverses the fixed stage-score order; the second
is the injective converse-orbit tie code. Its order is total on every
original fine-colour palette, with no shared artificial cross-sort order.
-/

universe u v w z t
namespace CCO.Selectors
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {Λ : Type z} [Group Λ] {N : Type t}

/-- Smaller lex keys are earlier priorities: higher global score first,
then the fixed converse-compatible tie code. -/
noncomputable def priorityKey (A : PureTagAction S Λ N)
    {J K : Family S} {n : Nat}
    (chain : DescentChain S (IsVisibleGate S A) J K n)
    {i j : ι} (a : S.Atom i j) : Lex (OrderDual Nat × Nat) :=
  toLex (OrderDual.toDual (descentScore S A chain a), atomTie S a)

theorem priorityKey_injective (A : PureTagAction S Λ N)
    {J K : Family S} {n : Nat}
    (chain : DescentChain S (IsVisibleGate S A) J K n)
    (i j : ι) :
    Function.Injective (priorityKey S A chain (i := i) (j := j)) := by
  intro a b h
  have ht : atomTie S a = atomTie S b := by
    have hp := congrArg (fun p : Lex (OrderDual Nat × Nat) => (ofLex p).2) h
    exact hp
  exact atomTie_injective S i j ht

theorem priorityKey_reverse (A : PureTagAction S Λ N)
    {J K : Family S} {n : Nat}
    (chain : DescentChain S (IsVisibleGate S A) J K n)
    {i j : ι} (a : S.Atom i j) :
    priorityKey S A chain (S.conv a) = priorityKey S A chain a := by
  unfold priorityKey
  rw [descentScore_reverse S A chain a, atomTie_reverse S a]

/-- The actual total priority order on each original hom-palette. -/
noncomputable def priorityOrder (A : PureTagAction S Λ N)
    {J K : Family S} {n : Nat}
    (chain : DescentChain S (IsVisibleGate S A) J K n)
    (i j : ι) : LinearOrder (S.Atom i j) :=
  LinearOrder.lift' (fun a : S.Atom i j => priorityKey S A chain a)
    (priorityKey_injective S A chain i j)

theorem priorityOrder_le_iff (A : PureTagAction S Λ N)
    {J K : Family S} {n : Nat}
    (chain : DescentChain S (IsVisibleGate S A) J K n)
    {i j : ι} (a b : S.Atom i j) :
    @LE.le (S.Atom i j) (priorityOrder S A chain i j).toLE a b ↔
      priorityKey S A chain a ≤ priorityKey S A chain b := by
  rfl

theorem priorityOrder_opposite (A : PureTagAction S Λ N)
    {J K : Family S} {n : Nat}
    (chain : DescentChain S (IsVisibleGate S A) J K n)
    {i j : ι} (a b : S.Atom i j) :
    @LE.le (S.Atom i j) (priorityOrder S A chain i j).toLE a b ↔
    @LE.le (S.Atom j i) (priorityOrder S A chain j i).toLE
      (S.conv a) (S.conv b) := by
  rw [priorityOrder_le_iff S A chain, priorityOrder_le_iff S A chain,
    priorityKey_reverse S A chain a, priorityKey_reverse S A chain b]

theorem terminal_priority_minimum (A : PureTagAction S Λ N)
    {K : Family S} {n : Nat}
    (chain : DescentChain S (IsVisibleGate S A) (originalFamily S) K n)
    (hTerm : Terminal S K)
    {i j : ι} (D : S.Menu i j) (hD : StrongExact.Exact S D)
    (b : S.Atom i j) (hb : b ∈ D) :
    @LE.le (S.Atom i j) (priorityOrder S A chain i j).toLE
      ((selectorOfTerminal S hTerm (DescentChain.composite chain)).choose D hD) b := by
  let h := selectorOfTerminal S hTerm (DescentChain.composite chain)
  let a := h.choose D hD
  by_cases heq : b = a
  · subst b
    exact (priorityOrder S A chain i j).le_refl a
  · have hs : descentScore S A chain b < descentScore S A chain a :=
      terminal_descent_strict_winner S A chain hTerm D hD b hb heq
    have hk : priorityKey S A chain a < priorityKey S A chain b := by
      apply (Prod.Lex.toLex_lt_toLex).2
      left
      exact hs
    exact (priorityOrder_le_iff S A chain a b).2 (le_of_lt hk)

/-- Package a joint selector together with genuine total orders which select
its minima and commute with the original atom converses. All hereditary,
PC and opposite fields remain part of the original selector structure. -/
structure PrioritySelector where
  selector : HereditarySelector S
  orders : ∀ i j : ι, LinearOrder (S.Atom i j)
  minimum : ∀ {i j : ι} (D : S.Menu i j)
      (hD : StrongExact.Exact S D) (b : S.Atom i j), b ∈ D →
      @LE.le (S.Atom i j) (orders i j).toLE (selector.choose D hD) b
  opposite_order : ∀ {i j : ι} (a b : S.Atom i j),
      @LE.le (S.Atom i j) (orders i j).toLE a b ↔
      @LE.le (S.Atom j i) (orders j i).toLE (S.conv a) (S.conv b)

/-- No standalone abstract hereditary selector is linearized: this result
uses the actual global gate chain as the witness. -/
noncomputable def prioritySelectorOfTerminal (A : PureTagAction S Λ N)
    {K : Family S} {n : Nat}
    (chain : DescentChain S (IsVisibleGate S A) (originalFamily S) K n)
    (hTerm : Terminal S K) : PrioritySelector S where
  selector := selectorOfTerminal S hTerm (DescentChain.composite chain)
  orders := fun i j => priorityOrder S A chain i j
  minimum := by
    intro i j D hD b hb
    exact terminal_priority_minimum S A chain hTerm D hD b hb
  opposite_order := by
    intro i j a b
    exact priorityOrder_opposite S A chain a b

/-- FG/LEX source consequence of C27 under the EXACT original hypotheses:
homogeneous finite-named symmetric strong-diversity SAP, semantic CCO, and
sortwise FULL original NR2. The atom priorities form compatible TOTAL
orders and their minimum selector preserves every original PC triple. -/
theorem exists_priority_selector_of_SAP_CCO_NR2
    {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,0,w} S) (nr2 : OriginalNR2 S) :
    Nonempty (PrioritySelector S) := by
  let C := exactCalculus_of_SAP_CCO S H sap cco
  let A := PureTagAction.trivial (S := S)
  have hNR : FullNoReturn S := by
    intro i j B D hB hD hGen
    exact fullNoReturn_of_nr2 S C H sap (fullNR2_of_original S H nr2)
      (i := i) (j := j) B D hB hD hGen
  have hInv : A.Invariant (originalFamily S) := by
    intro g D hD
    exact hD
  obtain ⟨K,hK,hKI,hTerm,n,hBound,chain,hCov⟩ :=
    pure_gate_iteration S C (S.realPointGluing_of_SAP H sap)
      (S.realEdgeGluing_of_SAP H sap) A (pureNoReturn_trivial S C hNR)
      (originalFamily S) (originalFamily_current S C) hInv
  exact ⟨prioritySelectorOfTerminal S A chain hTerm⟩

/-- Realized three-distinct-vertex triangle consumer, with no new provider. -/
theorem priority_source_joint_triangle_selection
    {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,0,w} S) (nr2 : OriginalNR2 S) :
    ∃ h : PrioritySelector S,
      ∀ (i j k : ι) (A : S.Menu i j) (B : S.Menu j k) (D : S.Menu i k)
      (hA : StrongExact.Exact S A) (hB : StrongExact.Exact S B)
      (hD : StrongExact.Exact S D),
      S.PC A B D →
        S.Triangle (h.selector.choose A hA) (h.selector.choose B hB)
          (h.selector.choose D hD) := by
  obtain ⟨h⟩ := exists_priority_selector_of_SAP_CCO_NR2 S H sap cco nr2
  exact ⟨h, fun i j k A B D hA hB hD hp =>
    h.selector.triangle S A B D hA hB hD hp⟩

end CCO.Selectors
