import CCO.RawExact.CanonicalQuotientSource
import CCO.RawExact.ActualQuotientSource
import CCO.RawExact.QuotientZeroWord
import CCO.RawExact.QuotientExpansionProjection

/-!
# The actual canonical quotient expansion menus and completed readout

Every specified actual quotient atom gets its genuine nonempty full-exact
original pullback presentation from C14. Missing edges get an empty Top
menu. Canonical identity-sort uniqueness proves every listed word has
positive diversity length. Thus neither exact-menu representation nor
positivity nor projected readout remains a provider in the final C27
assembly; the separate raw cycle witness/completion theorem is still
required to supply the original expansion homomorphism.
-/

universe v w t

namespace CCO.RawExact.CanonicalQuotientExpansion

open CanonicalQuotients

variable {A : Type v}
variable (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable {family : Finset (Setoid A)} (E : ExactData S family)

include cco

private theorem exact_atom_data {k l : Index family}
    (a : (CanonicalQuotients.source S H E).Atom k l) :
    ∃ B : NonemptyExact S () (),
      evaluate S B.words = GroupActions.pullback (projection k) (projection l)
        ((CanonicalQuotients.source S H E).atomRel a) ∧
      ∀ word ∈ B.words, 0 < diversityLength S word := by
  classical
  let : ∀ k : Index family, Invariant G k.val := ExactData.invariant S H E
  let : ∀ k : Index family, MulAction G (Carrier k) := action S H E
  let T := CanonicalQuotients.source S H E
  obtain ⟨q, r, hColour⟩ := T.realized a
  have hDiverse : (⟨k, q⟩ : Sigma (fun k : Index family => Carrier k)) ≠ ⟨l, r⟩ :=
    T.atomRel_ne hColour
  have hOrbit : T.atomRel a = GroupActions.orbital (G := G) q r := by
    funext x y
    apply propext
    change (T.colour x y = some a) ↔ GroupActions.orbital (G := G) q r x y
    constructor
    · intro hxy
      exact (source_colour_eq_iff_orbital S H E q r x y).mp (hColour.trans hxy.symm)
    · intro hxy
      exact ((source_colour_eq_iff_orbital S H E q r x y).mpr hxy).symm.trans hColour
  obtain ⟨x, hx⟩ := projection_surjective k q
  obtain ⟨y, hy⟩ := projection_surjective l r
  obtain ⟨B, hB⟩ := exact_actual_orbit_pullback_of_CCO S H cco
    (projection k) (projection l) (equivariant_projection S H E k)
    (equivariant_projection S H E l) (E.exact k) (E.exact l)
    (exact_kernel S E k) (exact_kernel S E l) x y
  have hOrbitalB : evaluate S B.words = GroupActions.pullback (projection k) (projection l)
      (GroupActions.orbital (G := G) q r) := by
    simpa only [hx, hy] using hB
  refine ⟨B, ?_, ?_⟩
  · exact hOrbitalB.trans (congrArg (GroupActions.pullback (projection k) (projection l)) hOrbit.symm)
  · intro word hWord
    exact actual_quotient_edge_word_positive S H k l q r hDiverse B hOrbitalB word hWord

noncomputable def atomExact {k l : Index family}
    (a : (CanonicalQuotients.source S H E).Atom k l) : NonemptyExact S () () :=
  (exact_atom_data S H cco E a).choose

theorem atomExact_represents {k l : Index family}
    (a : (CanonicalQuotients.source S H E).Atom k l) :
    evaluate S (atomExact S H cco E a).words =
      GroupActions.pullback (projection k) (projection l)
        ((CanonicalQuotients.source S H E).atomRel a) :=
  (exact_atom_data S H cco E a).choose_spec.1

theorem atomExact_positive {k l : Index family}
    (a : (CanonicalQuotients.source S H E).Atom k l) :
    ∀ word ∈ (atomExact S H cco E a).words, 0 < diversityLength S word :=
  (exact_atom_data S H cco E a).choose_spec.2

variable {n : Nat} (D : PartialDiagram (CanonicalQuotients.source S H E) (Fin n))

/-- One original source sort at every marked canonical quotient vertex. -/
def originalSort : Fin n → Unit := fun _ => ()

noncomputable def edgeExact (e : QuotientExpansion.Edge n) : NonemptyExact S () () :=
  match D.edge (QuotientExpansion.left e) (QuotientExpansion.right e)
      (QuotientExpansion.left_ne_right e) with
  | none => NonemptyExact.top S () ()
  | some a => atomExact S H cco E a

noncomputable def menus : QuotientExpansion.Menus S (originalSort (n := n)) :=
  fun e => (edgeExact S H cco E D e).words

theorem menus_nonempty : ∀ e, TRel.Nonempty (evaluate S (menus S H cco E D e)) :=
  fun e => (edgeExact S H cco E D e).nonempty

theorem menus_represents :
    QuotientExpansion.RepresentsEdges S (CanonicalQuotients.source S H E) D
      (fun _ => ()) projection (menus S H cco E D) := by
  intro e a hEdge
  cases hc : D.edge (QuotientExpansion.left e) (QuotientExpansion.right e)
      (QuotientExpansion.left_ne_right e) with
  | none => rw [hc] at hEdge; cases hEdge
  | some a' =>
      have ha : a' = a := Option.some.inj (hc.symm.trans hEdge)
      subst a'
      simpa only [menus, edgeExact, hc] using atomExact_represents S H cco E a

theorem menu_word_positive (e : QuotientExpansion.Edge n)
    (word : RawWord S () ()) (hWord : word ∈ menus S H cco E D e) :
    0 < diversityLength S word := by
  cases hc : D.edge (QuotientExpansion.left e) (QuotientExpansion.right e)
      (QuotientExpansion.left_ne_right e) with
  | none =>
      have hNil : menus S H cco E D e = [] := by
        simp only [menus, edgeExact, hc, NonemptyExact.top]
      rw [hNil] at hWord
      cases hWord
  | some a =>
      have hMem : word ∈ (atomExact S H cco E a).words := by
        simpa only [menus, edgeExact, hc] using hWord
      exact atomExact_positive S H cco E a word hMem

theorem menus_positive :
    ∀ o, 0 < diversityLength S
      (QuotientExpansion.word S (originalSort (n := n)) (menus S H cco E D) o) := by
  intro o
  exact menu_word_positive S H cco E D o.1 _ (List.get_mem _ o.2)

/-- Every choice of actual real representatives of a correctly coloured
quotient edge satisfies its entire source expansion menu. -/
theorem menu_holds_of_actual_edge (e : QuotientExpansion.Edge n)
    (a : (CanonicalQuotients.source S H E).Atom
      (D.vertexSort (QuotientExpansion.left e)) (D.vertexSort (QuotientExpansion.right e)))
    (hEdge : D.edge (QuotientExpansion.left e) (QuotientExpansion.right e)
      (QuotientExpansion.left_ne_right e) = some a)
    (x y : A)
    (hColour : (CanonicalQuotients.source S H E).colour
      (projection (D.vertexSort (QuotientExpansion.left e)) x)
      (projection (D.vertexSort (QuotientExpansion.right e)) y) = some a) :
    evaluate S (menus S H cco E D e) x y := by
  rw [menus_represents S H cco E D e a hEdge]
  exact hColour

/-- A word occurrence can only come from a genuinely specified quotient
edge: missing edges have empty Top menus, not fake identity restrictions. -/
theorem occurrence_specified
    (o : QuotientExpansion.Occurrence S (originalSort (n := n)) (menus S H cco E D)) :
    ∃ a, D.edge (QuotientExpansion.left o.1) (QuotientExpansion.right o.1)
      (QuotientExpansion.left_ne_right o.1) = some a := by
  cases hc : D.edge (QuotientExpansion.left o.1) (QuotientExpansion.right o.1)
      (QuotientExpansion.left_ne_right o.1) with
  | none =>
      have hNil : menus S H cco E D o.1 = [] := by
        simp only [menus, edgeExact, hc, NonemptyExact.top]
      have hBound := o.2.isLt
      have hLength : (menus S H cco E D o.1).length = 0 := congrArg List.length hNil
      omega
  | some a => exact ⟨a, rfl⟩

/-- Completed actual original diagrams project to the canonical actual
quotient diagram. Every menu and positivity premise is instantiated. -/
noncomputable def project_completed
    (f : DiagramHom (QuotientExpansion.diagram S (originalSort (n := n))
      (menus S H cco E D) (menus_nonempty S H cco E D))) : DiagramHom D :=
  QuotientExpansion.project_expansion_hom S (CanonicalQuotients.source S H E) D
    (fun _ => ()) projection (menus S H cco E D) (menus_nonempty S H cco E D)
    (menus_represents S H cco E D) (menus_positive S H cco E D) f

end CCO.RawExact.CanonicalQuotientExpansion
