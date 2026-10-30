import CCO.ExactCRT.CanonicalTypedQuotients
import CCO.RawExact.ZeroWordBoundary
import CCO.RawExact.QuotientExpansionProjection

/-!
# Actual typed quotient expansion menus and completed readout

Every specified actual quotient atom gets its genuine nonempty full-exact
original pullback presentation from accepted atomic-block provider. Missing edges get an empty Top
menu. Literal sort-preserving projection of tagged equality proves every listed word has
positive diversity length. Thus neither exact-menu representation nor
positivity nor projected readout remains a provider in the B041 C39
assembly; the separate raw cycle witness/completion theorem is still
required to supply the original expansion homomorphism.
-/

universe u v w q r t

namespace CCO.SimultaneousQuotients.CCOBranch.Menus

open CCO.RawExact

variable {ι : Type u} {X : ι → Type v} {Q : ι → Type q}
variable (S : AtomicSource.{u,v,w} ι X) (T : AtomicSource.{u,q,r} ι Q)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)] [∀ i, MulAction G (Q i)]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{u,v,max u v,w} S)
variable (π : ∀ i, X i → Q i) (surjπ : ∀ i, Function.Surjective (π i))
variable (equivπ : ∀ i (g : G) x, π i (g • x) = g • π i x)
variable (E : ∀ i, NonemptyExact S i i)
variable (hE : ∀ i, GroupActions.kernel (π i) = evaluate S (E i).words)
variable (hT : ∀ {i j} (x : Q i) (y : Q j) (x' : Q i) (y' : Q j),
  T.colour x y = T.colour x' y' ↔ GroupActions.orbital (G := G) x y x' y')

include H cco surjπ equivπ E hE hT

/-- A zero-diversity word forces tagged old equality, hence tagged quotient
 equality under the sort-preserving projections. This contradicts the actual
 quotient diversity atom. No duplicate-sort or capacity hypothesis occurs. -/
private theorem exact_atom_data {i j : ι} (a : T.Atom i j) :
    ∃ B : NonemptyExact S i j,
      evaluate S B.words = GroupActions.pullback (π i) (π j) (T.atomRel a) ∧
      ∀ word ∈ B.words, 0 < diversityLength S word := by
  obtain ⟨B, hB⟩ := ExactCRT.quotient_atom_pullback_exact S T H cco π surjπ equivπ E hE hT a
  refine ⟨B, hB, ?_⟩
  intro word hWord
  by_contra hPos
  have hZero : diversityLength S word = 0 := by omega
  obtain ⟨x, y, hxy⟩ := B.nonempty
  have hTag := (zeroLength_relation_iff_tagged_eq S word hZero x y).mp (hxy word hWord)
  have hAtom : T.atomRel a (π i x) (π j y) := by
    change GroupActions.pullback (π i) (π j) (T.atomRel a) x y
    rw [← hB]
    exact hxy
  apply T.atomRel_ne hAtom
  exact congrArg (fun p : Sigma X => (⟨p.1, π p.1 p.2⟩ : Sigma Q)) hTag

/-- Normalize a top pullback to the empty restriction list. Such an edge
keeps its two marked variables and attaches no private path. -/
noncomputable def atomExact {k l : ι}
    (a : T.Atom k l) : NonemptyExact S k l := by
  classical
  exact if GroupActions.pullback (π k) (π l) (T.atomRel a) = TRel.top X k l then
    NonemptyExact.top S k l
  else (exact_atom_data S T H cco π surjπ equivπ E hE hT a).choose

theorem atomExact_represents {k l : ι}
    (a : T.Atom k l) :
    evaluate S (atomExact S T H cco π surjπ equivπ E hE hT a).words =
      GroupActions.pullback (π k) (π l) (T.atomRel a) := by
  classical
  unfold atomExact
  split_ifs with hTop
  · exact (evaluate_nil S).trans hTop.symm
  · exact (exact_atom_data S T H cco π surjπ equivπ E hE hT a).choose_spec.1

theorem atomExact_top_words {k l : ι} (a : T.Atom k l)
    (hTop : GroupActions.pullback (π k) (π l) (T.atomRel a) = TRel.top X k l) :
    (atomExact S T H cco π surjπ equivπ E hE hT a).words = [] := by
  classical
  simp only [atomExact, ite_eq_left hTop, NonemptyExact.top]

theorem atomExact_positive {k l : ι}
    (a : T.Atom k l) :
    ∀ word ∈ (atomExact S T H cco π surjπ equivπ E hE hT a).words,
      0 < diversityLength S word := by
  classical
  unfold atomExact
  split_ifs with hTop
  · simp [NonemptyExact.top]
  · exact (exact_atom_data S T H cco π surjπ equivπ E hE hT a).choose_spec.2

variable {n : Nat} (D : PartialDiagram T (Fin n))

noncomputable def edgeExact (e : QuotientExpansion.Edge n) : NonemptyExact S (D.vertexSort (QuotientExpansion.left e))
      (D.vertexSort (QuotientExpansion.right e)) :=
  match D.edge (QuotientExpansion.left e) (QuotientExpansion.right e)
      (QuotientExpansion.left_ne_right e) with
  | none => NonemptyExact.top S _ _
  | some a => atomExact S T H cco π surjπ equivπ E hE hT a

noncomputable def menus : QuotientExpansion.Menus S D.vertexSort :=
  fun e => (edgeExact S T H cco π surjπ equivπ E hE hT D e).words

theorem menus_nonempty : ∀ e, TRel.Nonempty (evaluate S (menus S T H cco π surjπ equivπ E hE hT D e)) :=
  fun e => (edgeExact S T H cco π surjπ equivπ E hE hT D e).nonempty

theorem menus_represents :
    QuotientExpansion.RepresentsEdges S T D
      id π (menus S T H cco π surjπ equivπ E hE hT D) := by
  intro e a hEdge
  cases hc : D.edge (QuotientExpansion.left e) (QuotientExpansion.right e)
      (QuotientExpansion.left_ne_right e) with
  | none => rw [hc] at hEdge; cases hEdge
  | some a' =>
      have ha : a' = a := Option.some.inj (hc.symm.trans hEdge)
      subst a'
      simpa only [menus, edgeExact, hc, QuotientExpansion.markedOriginalSort, id_eq] using atomExact_represents S T H cco π surjπ equivπ E hE hT a

theorem menu_word_positive (e : QuotientExpansion.Edge n)
    (word : RawWord S (D.vertexSort (QuotientExpansion.left e))
      (D.vertexSort (QuotientExpansion.right e))) (hWord : word ∈ menus S T H cco π surjπ equivπ E hE hT D e) :
    0 < diversityLength S word := by
  cases hc : D.edge (QuotientExpansion.left e) (QuotientExpansion.right e)
      (QuotientExpansion.left_ne_right e) with
  | none =>
      have hNil : menus S T H cco π surjπ equivπ E hE hT D e = [] := by
        simp only [menus, edgeExact, hc, NonemptyExact.top]
      rw [hNil] at hWord
      cases hWord
  | some a =>
      have hMem : word ∈ (atomExact S T H cco π surjπ equivπ E hE hT a).words := by
        simpa only [menus, edgeExact, hc] using hWord
      exact atomExact_positive S T H cco π surjπ equivπ E hE hT a word hMem

theorem menus_positive :
    ∀ o, 0 < diversityLength S
      (QuotientExpansion.word S D.vertexSort (menus S T H cco π surjπ equivπ E hE hT D) o) := by
  intro o
  exact menu_word_positive S T H cco π surjπ equivπ E hE hT D o.1 _ (List.get_mem _ o.2)

/-- Every choice of actual real representatives of a correctly coloured
quotient edge satisfies its entire source expansion menu. -/
theorem menu_holds_of_actual_edge (e : QuotientExpansion.Edge n)
    (a : T.Atom
      (D.vertexSort (QuotientExpansion.left e)) (D.vertexSort (QuotientExpansion.right e)))
    (hEdge : D.edge (QuotientExpansion.left e) (QuotientExpansion.right e)
      (QuotientExpansion.left_ne_right e) = some a)
    (x : X (D.vertexSort (QuotientExpansion.left e)))
    (y : X (D.vertexSort (QuotientExpansion.right e)))
    (hColour : T.colour
      (π (D.vertexSort (QuotientExpansion.left e)) x)
      (π (D.vertexSort (QuotientExpansion.right e)) y) = some a) :
    evaluate S (menus S T H cco π surjπ equivπ E hE hT D e) x y := by
  have hr := menus_represents S T H cco π surjπ equivπ E hE hT D e a hEdge
  change evaluate S (menus S T H cco π surjπ equivπ E hE hT D e) =
    GroupActions.pullback (π (D.vertexSort (QuotientExpansion.left e)))
      (π (D.vertexSort (QuotientExpansion.right e))) (T.atomRel a) at hr
  rw [hr]
  exact hColour

/-- A word occurrence can only come from a genuinely specified quotient
edge: missing edges have empty Top menus, not fake identity restrictions. -/
theorem occurrence_specified
    (o : QuotientExpansion.Occurrence S D.vertexSort (menus S T H cco π surjπ equivπ E hE hT D)) :
    ∃ a, D.edge (QuotientExpansion.left o.1) (QuotientExpansion.right o.1)
      (QuotientExpansion.left_ne_right o.1) = some a := by
  cases hc : D.edge (QuotientExpansion.left o.1) (QuotientExpansion.right o.1)
      (QuotientExpansion.left_ne_right o.1) with
  | none =>
      have hNil : menus S T H cco π surjπ equivπ E hE hT D o.1 = [] := by
        simp only [menus, edgeExact, hc, NonemptyExact.top]
      have hBound := o.2.isLt
      have hLength : (menus S T H cco π surjπ equivπ E hE hT D o.1).length = 0 := congrArg List.length hNil
      omega
  | some a => exact ⟨a, rfl⟩

/-- Completed actual original diagrams project to the canonical actual
quotient diagram. Every menu and positivity premise is instantiated. -/
noncomputable def project_completed
    (f : DiagramHom (QuotientExpansion.diagram S D.vertexSort
      (menus S T H cco π surjπ equivπ E hE hT D) (menus_nonempty S T H cco π surjπ equivπ E hE hT D))) : DiagramHom D :=
  QuotientExpansion.project_expansion_hom S T D
    id π (menus S T H cco π surjπ equivπ E hE hT D) (menus_nonempty S T H cco π surjπ equivπ E hE hT D)
    (menus_represents S T H cco π surjπ equivπ E hE hT D) (menus_positive S T H cco π surjπ equivπ E hE hT D) f

end CCO.SimultaneousQuotients.CCOBranch.Menus
