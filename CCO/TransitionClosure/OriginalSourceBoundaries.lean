import CCO.TransitionClosure.TypedIdentityExterior
import CCO.TerminalLattice.FibreSAP

/-!
# B049 source07 C54/C60: finite non-SAP and zero-diversity boundaries

The genuine positive old RAW/STRONG saturation theorem requires OLD SAP.
On an ACTUAL two-point old diversity carrier, the equality-inclusive
RAW J;t;K relation for J=K=Top has a distinct endpoint pair because
the one old t-edge exists. Its STRONG profile with THREE genuinely
diversity edges and FOUR distinct formal positions cannot have ANY
realization on two old points. This is only a finite negative boundary,
not a claim that a bounded check proves original unbounded SAP/CCO.

The other source boundary is exact: with NO original same-sort
diversity atoms there can be NO genuinely nonidentity original FULL
invariant equivalence. This follows directly from the accepted
B050 original actual nonzero-equivalence pair lemma and the real
OLD full-colour source, not a hidden quotient age.

The identity-exterior case remains the positive SOURCE theorem in
TypedIdentityExterior: equality factors must be OMITTED, never
replaced by an empty STRONG factor or a fake diversity identity.

No new axiom, sorry, quotient SAP/CCO or change of pinned input.
-/

universe u v w

namespace CCO.TransitionClosure

/-- The two old points of the C54 finite obstruction. -/
def oldTwoPointRAW (x z : Bool) : Prop :=
  ∃ u v : Bool, True ∧ u ≠ v ∧ True

/-- Actual three-edge STRONG walk for four ALL-DISTINCT
formal positions on the two-point old carrier. -/
def oldTwoPointSTRONG (x z : Bool) : Prop :=
  x ≠ z ∧ ∃ u v : Bool,
    x ≠ u ∧ u ≠ v ∧ v ≠ z ∧
      x ≠ v ∧ u ≠ z

/-- C54 source counterexample, LEFT: the original two-point
old K2 diversity relation has a true equality-inclusive
RAW three-step witness between DISTINCT real endpoints. -/
theorem oldTwoPointRAW_nonempty_diversity :
    oldTwoPointRAW false true := by
  exact ⟨false,true,trivial,by decide,trivial⟩

/-- C54 source counterexample, RIGHT: FOUR mutually distinct
formal positions cannot be represented by just TWO points,
so the three-diversity-edge STRONG profile is empty.
No assertion that the K2 age has SAP is made. -/
theorem oldTwoPointSTRONG_missing_diversity :
    ¬ oldTwoPointSTRONG false true := by
  intro h
  obtain ⟨_,u,v,hxu,_,_,_,huz⟩ := h
  cases u <;> simp_all

/-- Explicit failure of RAW⇒STRONG if original SAP is
dropped: no bounded finite model may substitute for the
unbounded real original SAP proof of source TSC. -/
theorem oldTwoPointRAW_not_STRONG :
    oldTwoPointRAW false true ∧ ¬ oldTwoPointSTRONG false true :=
  ⟨oldTwoPointRAW_nonempty_diversity,
    oldTwoPointSTRONG_missing_diversity⟩

/-- C60: an ORIGINAL old sort with no same-sort realised
diversity atomic colour admits NO nonzero full invariant
equivalence at all. If J>Id, B050 gives an actually
distinct J-pair; original complete OLD colours then give
a genuine fine diversity atom, contradiction.

The theorem is in the FULL original ColourEq lattice, not
a represented fragment and not an inference on hidden sorts. -/
theorem original_no_nonzero_full_equiv_of_no_diversity
    {ι : Type u} {X : ι → Type v}
    (S : AtomicSource.{u,v,w} ι X)
    {i : ι} (hNo : IsEmpty (S.Atom i i))
    (J : ParityHasse.Original.ColourEq S i) :
    ¬ (⊥ : ParityHasse.Original.ColourEq S i) < J := by
  letI : IsEmpty (S.Atom i i) := hNo
  intro hJ
  obtain ⟨x,y,_,hne⟩ :=
    TerminalLattice.actual_nontrivial_equiv_pair S J hJ
  have hTag : (⟨i,x⟩ : Sigma X) ≠ ⟨i,y⟩ := by
    intro h
    exact hne (by
      simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using h)
  obtain ⟨a,_⟩ := S.some_colour_of_ne x y hTag
  exact isEmptyElim a

end CCO.TransitionClosure
