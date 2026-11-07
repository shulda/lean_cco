import CCO.UnfilteredEP.CoreWitnesses

/-!
# B064 C01–C13: simultaneous-singleton finite core criterion

This theorem is independent of CCO and all source-specific providers.
It retains the actual original sorts and fine atom names. All allowed
pairs, including repeated labels on distinct vertices, are stored in one
finite JEP witness. A single old host is chosen before EVERY competitor.
-/

universe u v w z p q
namespace CCO.UnfilteredEP.FiniteAge
variable {OldSort : Type u} {Atom : Type v} {Label : Type p}
variable (K : FiniteAge.{u,v,w,z} OldSort Atom)
variable (T : FiniteTemplate OldSort Atom Label)

/-- A missing label in a table endomorphism defeats every proposed old
host. Ramsey, JEP, CCO and amalgamation are unnecessary for this direction. -/
theorem finite_template_core_of_unary_EP [Finite Label]
    (realized : ∀ t : Label, ∃ (A : K.Obj) (a : K.Marking T A) (x : K.Point A), a.label x = t)
    (surjective : K.ReductSurjective T) (ep : K.UnaryEP T) : T.Core := by
  classical
  intro f hf
  apply T.automorphism_of_injective f hf
  apply Finite.injective_iff_surjective.mpr
  intro t
  obtain ⟨A,a,x,hx⟩ := realized t
  obtain ⟨B,hB⟩ := ep A a
  obtain ⟨b⟩ := surjective B
  obtain ⟨e⟩ := hB (b.postcompose f hf)
  exact ⟨b.label (e.old.toFun x),(e.labels x).trans hx⟩

/-- With no labels, every legal old object is empty, and the same old
object is already a universal host for its uniquely marked copy. -/
theorem unary_EP_of_empty_labels [IsEmpty Label] : K.UnaryEP T := by
  intro A a
  refine ⟨A,?_⟩
  intro b
  refine ⟨⟨Embedding.id A,?_⟩⟩
  intro x
  exact isEmptyElim (a.label x)

namespace RamseyProvider
variable {K T} (P : K.RamseyProvider.{u,v,w,z,p,q} T)

/-- Every competitor restricts, on the selected D copy, to one actual
template endomorphism. The stored inverse-target copy then recovers A. -/
theorem unary_EP_of_finite_template_core [Finite Label] [Finite Atom]
    (S : P.Singletons) (lift : P.ReductSurjective) (jep : P.JEP)
    (ramsey : P.Ramsey) (pairs : K.AllPairsRealized T) (core : T.Core) :
    K.UnaryEP T := by
  classical
  cases isEmpty_or_nonempty Label with
  | inl hEmpty =>
    let _ := hEmpty
    exact unary_EP_of_empty_labels K T
  | inr hNonempty =>
    let _ := hNonempty
    intro A a
    obtain ⟨W⟩ := P.coreWitnesses_exists S lift jep pairs a
    obtain ⟨C,hC⟩ := P.simultaneous_singletons S ramsey W.object
    refine ⟨P.old C,?_⟩
    intro b
    let colour : ∀ t, P.Embedding (S.object t) C → Label :=
      fun t e => b.label (e.val.old.toFun (S.point t))
    obtain ⟨g,hg⟩ := hC colour
    let f : Label → Label := fun t =>
      b.label (g.val.old.toFun ((W.singleton t).val.old.toFun (S.point t)))
    have value (x : K.Point (P.old W.object)) :
        b.label (g.val.old.toFun x) = f ((P.marking W.object).label x) := by
      obtain ⟨e,he⟩ := S.at_vertex W.object x
      have h := hg ((P.marking W.object).label x) e
        (W.singleton ((P.marking W.object).label x))
      change b.label (g.val.old.toFun (e.val.old.toFun
        (S.point ((P.marking W.object).label x)))) = _ at h
      simpa only [colour, Embedding.comp, MarkedEmbedding.comp, FiniteAge.Embedding.comp, Function.comp_apply, he] using h
    have hf : T.Endomorphism f := by
      constructor
      · intro t
        let x := (W.singleton t).val.old.toFun (S.point t)
        have hx : (P.marking W.object).label x = t :=
          ((W.singleton t).val.labels (S.point t)).trans (S.labelled t)
        change T.sort (b.label (g.val.old.toFun x)) = T.sort t
        exact (b.sorted _).trans ((g.val.old.sorted x).trans
          (((P.marking W.object).sorted x).symm.trans (congrArg T.sort hx)))
      · intro r s t hst
        let pair : PairIndex (T := T) := ⟨(r,s,t),hst⟩
        have hcol : K.colour (P.old C)
            (g.val.old.toFun (W.left pair)) (g.val.old.toFun (W.right pair)) = some r :=
          (g.val.old.colours _ _).trans (W.colour pair)
        have hpair := b.pairs _ _ r hcol
        rw [value, value, W.left_label pair, W.right_label pair] at hpair
        exact hpair
    have ha := core f hf
    let alpha : AutomorphismIndex (T := T) := ⟨f,ha⟩
    let e := W.inverse alpha
    refine ⟨⟨g.val.old.comp e.old,?_⟩⟩
    intro x
    change b.label (g.val.old.toFun (e.old.toFun x)) = a.label x
    rw [value, e.labels x]
    exact (T.automorphismEquiv ha).apply_symm_apply (a.label x)

/-- U2, with all A01 inputs explicit. Provider singletons are genuine
one-point objects and all pair-table entries have actual distinct-point
witnesses. No CCO or terminal source assumption occurs. -/
theorem finite_core_criterion [Finite Label] [Finite Atom]
    (S : P.Singletons) (oldSurjective : K.ReductSurjective T)
    (lift : P.ReductSurjective) (jep : P.JEP) (ramsey : P.Ramsey)
    (pairs : K.AllPairsRealized T) : K.UnaryEP T ↔ T.Core := by
  constructor
  · intro ep
    apply finite_template_core_of_unary_EP K T _ oldSurjective ep
    intro t
    exact ⟨P.old (S.object t),P.marking (S.object t),S.point t,S.labelled t⟩
  · exact P.unary_EP_of_finite_template_core S lift jep ramsey pairs

end RamseyProvider
end CCO.UnfilteredEP.FiniteAge
