import CCO.ParityHasse.Relative.Separation
import CCO.ParityHasse.Relative.NamedQuotient

/-! Source-level consumers of the two INDEPENDENT B007 branches.
No SAP, countability, NR2, Hasse, CRT, rigid character or quotient lifting
provider is a hypothesis. Exact Y and its odd complement are the intended
explicit hypotheses of the maximal-gate theorem; its upper U need not be exact. -/
universe u v w t
namespace CCO.ParityHasse.Relative
open Original
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) {i : ι}
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]
variable (H : HomogeneousSource S G)
variable (cco : SemanticCCO.{u,v,max u v,w} S)

include H cco in
/-- C15–19 downstream API: the actual stable powers are exact invariant
equivalences and their actual meet is K. -/
theorem separated_exact_closures (K : ColourEq S i) (hK : Exact S K)
    (A B : Rel (X i)) (hA : Exact S A) (hB : Exact S B)
    (hKA : K ≤ A) (hKB : K ≤ B)
    (satA : Bisaturated K.val A) (satB : Bisaturated K.val B)
    (hAB : (fun x y => A x y ∧ B x y) = K) :
    ∃ CA CB : ColourEq S i, Exact S CA ∧ Exact S CB ∧
      CA ⊓ CB = K ∧
      (∃ n, CA = power K.val A n) ∧ (∃ n, CB = power K.val B n) := by
  let CA := closureEq S H K A (hA.colourInvariant S H) satA
  let CB := closureEq S H K B (hB.colourInvariant S H) satB
  refine ⟨CA,CB,closure_exact S H cco K hK A hA hKA,
    closure_exact S H cco K hK B hB hKB,?_,?_,?_⟩
  · apply ColourEq.ext
    intro x y
    exact iff_of_eq (congrFun (congrFun (closure_separation S H cco K hK A B hA hB hKA hKB satA satB hAB) x) y)
  · obtain ⟨n,hn,_⟩ := closure_stabilizes S H K A (hA.colourInvariant S H) hKA
    exact ⟨n,hn⟩
  · obtain ⟨n,hn,_⟩ := closure_stabilizes S H K B (hB.colourInvariant S H) hKB
    exact ⟨n,hn⟩

/-- Literal named-quotient output, whose selected exact presentation is
constructed from the actual involution orbital. -/
def NamedGateData (Y U : ColourEq S i) (M : MaximalGate S H Y U) : Prop :=
  letI := quotientAction S H M.kernel
  let π := Quotient.mk M.kernel.val
  let surj : Function.Surjective π := Quotient.mk_surjective
  let equivπ := quotientProjection_equivariant S H M.kernel
  ∃ D : RawExact.NonemptyExact (namedQuotient S H π surj equivπ) () (),
    RawExact.evaluate (namedQuotient S H π surj equivπ) D.words = imageRelation π (gate S M.kernel U Y) ∧
    ∃ I : InvolutionGraph (imageRelation π (gate S M.kernel U Y)),
      (∀ (g : G) q, I.map (g • q) = g • I.map q) ∧
      ∀ Z : Setoid (Quotient M.kernel.val),
        (∃ P : RawExact.NonemptyExact (namedQuotient S H π surj equivπ) () (),
          RawExact.evaluate (namedQuotient S H π surj equivπ) P.words = Z) →
        (⊥ : Setoid _) < Z → ∀ q r, imageRelation π (gate S M.kernel U Y) q r → Z q r

include H cco in
/-- C21–26 source headline, including actual M/K named RAW exactness,
quotient involution, all-exact dominance and the ORIGINAL nonidentity bridge.
Every conditional helper is discharged from the displayed source data. -/
theorem source_maximal_exact_gate (Y U : ColourEq S i) (hY : Exact S Y) (hYU : Y ≤ U)
    (hO : Exact S (odd Y.val U.val)) (a : X i)
    (htwo : relativeIndex Y.val U.val a = 2) :
    ∃ M : MaximalGate S H Y U, NamedGateData S H Y U M ∧
      Nonempty (ExactIsotropyBridge S M.kernel) := by
  obtain ⟨M⟩ := exists_maximalGate S H cco Y U hY hYU hO a htwo
  refine ⟨M,?_,maximalGate_bridge S H Y U M⟩
  letI := quotientAction S H M.kernel
  let π := Quotient.mk M.kernel.val
  have surj : Function.Surjective π := Quotient.mk_surjective
  have equivπ := quotientProjection_equivariant S H M.kernel
  have hk : GroupActions.kernel π = M.kernel := by
    funext x y; exact propext Quotient.eq
  obtain ⟨D,hD⟩ := namedQuotient_gate_exact S H Y U M π surj equivπ hk (π a)
  refine ⟨D,hD,quotientGateInvolution S H Y U M π surj hk,
    quotientGateInvolution_equivariant S H Y U M π surj equivπ hk,?_⟩
  rintro Z ⟨P,hP⟩ hZ
  exact namedQuotient_gate_dominance S H cco Y U M π surj equivπ hk Z P hP hZ

end CCO.ParityHasse.Relative
