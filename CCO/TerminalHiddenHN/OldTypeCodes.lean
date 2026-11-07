import CCO.TerminalHiddenHN.Interpretation

/-! The COMPLETE non-order term code is determined by the original
optional pair colour. The true diagonal is included. Only original pair
homogeneity and the literal equivariant interpretation are used: no SAP,
NR2, cover, CCO, hidden amalgamation or Ramsey premise occurs. -/

universe u v w r l k
namespace CCO.TerminalHiddenHN.RealInterpretation
open CCO.UnaryFreshFrames
variable {ι : Type u} {X : ι → Type v} {S : CCO.AtomicSource.{u,v,w} ι X}
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable {U : Language.{max u l}} {V : Type k} {P : Structure U V}
variable (D : RealInterpretation (G := G) S U P)

def rootTermValue {i : ι} {a : U.Sorts} (q : Term U (D.realSort i) a) (x : X i) : V :=
  P.eval q (D.root i x).val

theorem rootTermValue_sort {i : ι} {a : U.Sorts}
    (q : Term U (D.realSort i) a) (x : X i) : P.sort (D.rootTermValue q x) = a :=
  P.eval_sort q (D.root i x).property

theorem rootTermValue_equivariant (g : G) {i : ι} {a : U.Sorts}
    (q : Term U (D.realSort i) a) (x : X i) :
    (D.motion g) • D.rootTermValue q x = D.rootTermValue q (g • x) :=
  (P.aut_eval (D.motion g) q (D.root i x).val).trans
    (congrArg (P.eval q) (D.root_equivariant g i x))

/-- One ORIGINAL group element simultaneously moves both evaluated
terms. Optional pair-colour equality includes repeated-root tuples. -/
theorem old_colour_term_pair_motion (H : CCO.HomogeneousSource S G)
    {i j : ι} {a b : U.Sorts}
    (q : Term U (D.realSort i) a) (t : Term U (D.realSort j) b)
    (x x' : X i) (y y' : X j) (h : S.colour x y = S.colour x' y') :
    ∃ g : G, (D.motion g) • D.rootTermValue q x = D.rootTermValue q x' ∧
      (D.motion g) • D.rootTermValue t y = D.rootTermValue t y' := by
  obtain ⟨g,hx,hy⟩ := S.pair_homogeneous_of_homogeneous H x x' y y' h
  exact ⟨g,(D.rootTermValue_equivariant g q x).trans (congrArg (D.rootTermValue q) hx),
    (D.rootTermValue_equivariant g t y).trans (congrArg (D.rootTermValue t) hy)⟩

theorem old_colour_term_equality (H : CCO.HomogeneousSource S G)
    {i j : ι} {a b : U.Sorts}
    (q : Term U (D.realSort i) a) (t : Term U (D.realSort j) b)
    (x x' : X i) (y y' : X j) (h : S.colour x y = S.colour x' y') :
    D.rootTermValue q x = D.rootTermValue t y ↔
      D.rootTermValue q x' = D.rootTermValue t y' := by
  obtain ⟨g,hq,ht⟩ := D.old_colour_term_pair_motion H q t x x' y y' h
  constructor
  · intro he
    exact hq.symm.trans ((congrArg (fun z => (D.motion g) • z) he).trans ht)
  · intro he
    apply MulAction.injective (D.motion g)
    exact hq.trans (he.trans ht.symm)

/-- Actual partial function graphs include their declared input-sort
condition; off-sort identity bookkeeping is not a displayed graph. -/
def functionGraphCode {i j : ι} {a b : U.Sorts} (F : U.Func)
    (q : Term U (D.realSort i) a) (t : Term U (D.realSort j) b) (x : X i) (y : X j) : Prop :=
  P.sort (D.rootTermValue q x) = U.input F ∧
    P.func F (D.rootTermValue q x) = D.rootTermValue t y

theorem old_colour_function_graph (H : CCO.HomogeneousSource S G)
    {i j : ι} {a b : U.Sorts} (F : U.Func)
    (q : Term U (D.realSort i) a) (t : Term U (D.realSort j) b)
    (x x' : X i) (y y' : X j) (h : S.colour x y = S.colour x' y') :
    D.functionGraphCode F q t x y ↔ D.functionGraphCode F q t x' y' := by
  obtain ⟨g,hq,ht⟩ := D.old_colour_term_pair_motion H q t x x' y y' h
  have hs : P.sort (D.rootTermValue q x') = P.sort (D.rootTermValue q x) :=
    hq ▸ P.aut_sort (D.motion g) (D.rootTermValue q x)
  have hf : (D.motion g) • P.func F (D.rootTermValue q x) = P.func F (D.rootTermValue q x') :=
    (P.aut_func (D.motion g) F _).trans (congrArg (P.func F) hq)
  constructor
  · rintro ⟨hin,hval⟩
    exact ⟨hs.trans hin,hf.symm.trans ((congrArg (fun z => (D.motion g) • z) hval).trans ht)⟩
  · rintro ⟨hin,hval⟩
    refine ⟨hs.symm.trans hin,?_⟩
    apply MulAction.injective (D.motion g)
    exact hf.trans (hval.trans ht.symm)

def binaryTermCode {i j : ι} {a b : U.Sorts} (R : U.Rel)
    (q : Term U (D.realSort i) a) (t : Term U (D.realSort j) b) (x : X i) (y : X j) : Prop :=
  P.rel R (fun n => if n.val = 0 then D.rootTermValue q x else D.rootTermValue t y)

/-- EVERY named hidden binary relation is retained, without a selected
cylinder restriction or a distinct-real-root guard. -/
theorem old_colour_binary_code (H : CCO.HomogeneousSource S G)
    {i j : ι} {a b : U.Sorts} (R : U.Rel)
    (q : Term U (D.realSort i) a) (t : Term U (D.realSort j) b)
    (x x' : X i) (y y' : X j) (h : S.colour x y = S.colour x' y') :
    D.binaryTermCode R q t x y ↔ D.binaryTermCode R q t x' y' := by
  obtain ⟨g,hq,ht⟩ := D.old_colour_term_pair_motion H q t x x' y y' h
  have hm : (fun z => (D.motion g) • z) ∘
      (fun n : Fin (U.arity R) => if n.val = 0 then D.rootTermValue q x else D.rootTermValue t y) =
      (fun n => if n.val = 0 then D.rootTermValue q x' else D.rootTermValue t y') := by
    funext n
    by_cases hn : n.val = 0 <;> simp only [Function.comp_apply,hn,if_true,if_false] <;> assumption
  have hr := P.aut_rel (D.motion g) R
    (fun n => if n.val = 0 then D.rootTermValue q x else D.rootTermValue t y)
  rw [hm] at hr
  exact hr.symm

/-- All non-order codes of the two marked roots, quantified over ALL
actual terms, graph symbols and binary names, not merely quotient incidence. -/
structure NonOrderCodeAgreement {i j : ι} (x x' : X i) (y y' : X j) : Prop where
  equality : ∀ (a b : U.Sorts) (q : Term U (D.realSort i) a) (t : Term U (D.realSort j) b),
    D.rootTermValue q x = D.rootTermValue t y ↔ D.rootTermValue q x' = D.rootTermValue t y'
  function_graph : ∀ F (a b : U.Sorts) (q : Term U (D.realSort i) a) (t : Term U (D.realSort j) b),
    D.functionGraphCode F q t x y ↔ D.functionGraphCode F q t x' y'
  binary : ∀ R (a b : U.Sorts) (q : Term U (D.realSort i) a) (t : Term U (D.realSort j) b),
    D.binaryTermCode R q t x y ↔ D.binaryTermCode R q t x' y'

theorem old_colour_complete_nonorder_codes (H : CCO.HomogeneousSource S G)
    {i j : ι} (x x' : X i) (y y' : X j) (h : S.colour x y = S.colour x' y') :
    D.NonOrderCodeAgreement x x' y y' := by
  exact {
    equality := fun _ _ q t => D.old_colour_term_equality H q t x x' y y' h
    function_graph := fun F _ _ q t => D.old_colour_function_graph H F q t x x' y y' h
    binary := fun R _ _ q t => D.old_colour_binary_code H R q t x x' y y' h }

end CCO.TerminalHiddenHN.RealInterpretation
