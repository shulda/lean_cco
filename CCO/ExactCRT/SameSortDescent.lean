import CCO.ExactCRT.Descent

/-! C21–22: the genuine single-original-sort source discharges each TI
certificate by original invariant commutation. Containment and endpoint
saturation remain displayed separately for the source descent statement. -/
universe v w q r t
namespace CCO.ExactCRT
open RawExact
variable {X : Unit → Type v} {Q : Unit → Type q}
variable (S : AtomicSource.{0,v,w} Unit X) (T : AtomicSource.{0,q,r} Unit Q)
variable {G : Type t} [Group G] [∀i, MulAction G (X i)] [∀i, MulAction G (Q i)]
variable (H : HomogeneousSource S G)
variable (E : ∀i, NonemptyExact S i i)
include H

/-- Actual original homogeneity gives pair-flips and therefore commutation
with every old atom. This is one-sort only; it proves the certificate. -/
theorem oneSort_wordTI {i j : Unit} (word : RawWord S i j) :
    WordTI S (fun i => evaluate S (E i).words) word := by
  apply wordTI_of_all_atoms S _
  intro i j a
  cases i
  cases j
  exact RawSymmetric.invariant_commute _ _
    (presentation_invariant_of_homogeneous S H (E ()).words)
    (S.rawAtomRel_invariant (some a) (S.colourInvariant_of_homogeneous H))
    (S.pair_flip_of_homogeneous H)

variable (π : ∀i, X i → Q i) (surjπ : ∀i, Function.Surjective (π i))
variable (equivπ : ∀i (g : G) x, π i (g • x) = g • π i x)
variable (hE : ∀i, GroupActions.kernel (π i) = evaluate S (E i).words)
variable (hT : ∀ {i j} (x : Q i) (y : Q j) (x' : Q i) (y' : Q j),
  T.colour x y = T.colour x' y' ↔ GroupActions.orbital (G := G) x y x' y')
include surjπ equivπ hE hT

/-- C21: the factorwise projected word identity, including nil and real
identity letters, with its commutation provider genuinely discharged. -/
theorem sameSort_projected_word_pullback {i j : Unit} (word : RawWord S i j) :
    GroupActions.pullback (π i) (π j)
      (RawWord.relation T (projectedWord S T π word)) =
      saturate (evaluate S (E i).words) (RawWord.relation S word)
        (evaluate S (E j).words) :=
  projectedWord_pullback_of_TI S T π H equivπ E hE hT surjπ word (oneSort_wordTI S H E word)

omit hT in
/-- C22 in the actual constructed quotient language. The source's
containment hypothesis is retained and does NOT replace saturation. -/
theorem actual_same_sort_exact_descent (cco : SemanticCCO.{0,v,v,w} S)
    {i : Unit} (D : NonemptyExact S i i)
    (_hContainment : ∀ x y, evaluate S (E i).words x y → evaluate S D.words x y)
    (hSat : saturate (evaluate S (E i).words) (evaluate S D.words)
      (evaluate S (E i).words) = evaluate S D.words) :
    letI := S.finiteSort
    ∃ F : NonemptyExact (TypedPalette.source Q S H id π surjπ equivπ) i i,
      evaluate (TypedPalette.source Q S H id π surjπ equivπ) F.words =
        quotientRelation (π i) (π i) (evaluate S D.words) := by
  apply actual_typed_exact_descent S H cco π surjπ equivπ E hE D hSat
  intro word _
  exact oneSort_wordTI S H E word

end CCO.ExactCRT
