import CCO.AutomaticEPCore.NonmaximalPhase
import CCO.AutomaticEPCore.FiniteCore
import CCO.AutomaticEPCore.TerminalLoopless

/-! The negative and positive C60 core conclusions on the ACTUAL old-atom
support tables. These use the concrete coordinate proofs and the generic
finite-relation lemma only. No genuine-tower automatic-core theorem or
unproved infinite source property certifies the nonmaximal construction. -/

namespace CCO.AutomaticEPCore.NonmaximalBoundary

open CCO.ParityHasse.Original

/-- The concrete old bipartite atoms are EXACTLY b and s, the two
bit-reversing atoms. The other two have genuine triangles in the
infinite old source; this is not a finite diagnostic inference. -/
theorem original_atom_bipartite_iff (a : Atom) :
    (atomGraph source (i := ()) a).IsBipartite ↔ a.2 = true := by
  rcases a with ⟨sameBlock,bitDifference⟩
  cases bitDifference with
  | false =>
    constructor
    · intro bipartite
      let point (n : Nat) : Point :=
        ⟨(if sameBlock then 0 else n,false),false,n⟩
      have edge01 : (atomGraph source (i := ()) (sameBlock,false)).Adj (point 0) (point 1) := by
        change colour (point 0) (point 1) = some (sameBlock,false)
        cases sameBlock <;> rfl
      have edge12 : (atomGraph source (i := ()) (sameBlock,false)).Adj (point 1) (point 2) := by
        change colour (point 1) (point 2) = some (sameBlock,false)
        cases sameBlock <;> rfl
      have edge20 : (atomGraph source (i := ()) (sameBlock,false)).Adj (point 2) (point 0) := by
        change colour (point 2) (point 0) = some (sameBlock,false)
        cases sameBlock <;> rfl
      have triangle : relPow (atomGraph source (i := ()) (sameBlock,false)).Adj 3
          (point 0) (point 0) :=
        ⟨point 1,edge01,point 2,edge12,point 0,edge20,rfl⟩
      exact False.elim
        (bipartite_graph_no_odd_power (atomGraph source (i := ()) (sameBlock,false))
          bipartite (point 0) 3 (by decide) triangle)
    · intro impossible
      cases impossible
  | true =>
    constructor
    · intro _
      rfl
    · intro _
      refine ⟨{ toFun := (fun x : Point => if x.bit then (1 : Fin 2) else 0), map_rel' := ?_ }⟩
      intro x y edge
      have bits : (x.bit ^^ y.bit) = true :=
        congrArg Prod.snd ((colour_some x y (sameBlock,true)).mp edge).2
      cases hx : x.bit <;> cases hy : y.bit <;> simp_all

/-- Literal old-atom support on the four realized labels of the
nonmaximal-first two-step source. Individual labels are not named in
the table language. -/
def actualNonmaximalTable (a : Atom) (p q : Label) : Prop :=
  ∃ x y : Point, label x = p ∧ label y = q ∧ colour x y = some a

/-- Two labels with the same actual mu bit have no ORIGINAL bipartite
separator, including the distinct same-mu/different-lambda labels. -/
theorem actual_nonmaximal_no_bipartite_separator (p q : Label)
    (sameMu : p.2 = q.2) :
    ¬∃ a : Atom, (atomGraph source (i := ()) a).IsBipartite ∧
      actualNonmaximalTable a p q := by
  rintro ⟨a,bipartite,pair⟩
  have bitOne := (original_atom_bipartite_iff a).mp bipartite
  have bits := ((table_iff_actual a p q).mpr pair).2
  rw [sameMu,Bool.xor_self,bitOne] at bits
  cases bits

theorem actual_nonmaximal_retract_preserves :
    TableEndomorphism actualNonmaximalTable retract := by
  intro a p q pair
  exact (table_iff_actual a (retract p) (retract q)).mp
    (retract_preserves a p q ((table_iff_actual a p q).mpr pair))

/-- The infinite source's ACTUAL four-label table is not a core: its
proved proper idempotent retraction preserves every original atom. -/
theorem actual_nonmaximal_table_not_core :
    ¬∀ f : Label → Label, TableEndomorphism actualNonmaximalTable f →
      TableAutomorphism actualNonmaximalTable f := by
  intro core
  exact retract_not_injective
    (core retract actual_nonmaximal_retract_preserves).1.1

namespace MaximalSplit

/-- Literal old-atom support of the SAME source with its actual FIRST
MAXIMAL gate. The carrier points are the genuine realized marked sorts. -/
def actualMaximalTable (a : Atom) (p q : Bool) : Prop :=
  ∃ x : Carrier (parentSort p), ∃ y : Carrier (parentSort q),
    colour x.val y.val = some a

/-- The actual first-maximal table is a core. Injection comes from its
explicit two-label atom supports; finite reflection uses the generic
finite-table lemma, never the source automatic-core theorem. -/
theorem actual_maximal_table_core (f : Bool → Bool)
    (preserves : TableEndomorphism actualMaximalTable f) :
    TableAutomorphism actualMaximalTable f := by
  apply finite_table_endomorphism_automorphism actualMaximalTable f preserves
  exact endomorphism_injective f (fun a p q pair => preserves a pair)

end MaximalSplit
end CCO.AutomaticEPCore.NonmaximalBoundary
