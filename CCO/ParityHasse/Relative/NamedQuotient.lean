import CCO.ParityHasse.Relative.QuotientGate
import CCO.RawExact.QuotientSourcePalette

/-! Bridge to the ACCEPTED actual quotient AtomicSource and RawWord API.
The auxiliary orbital-word spelling in QuotientWords is conservative:
every actual named RAW presentation is translated, retaining identity
letters, empty words, and empty lists of restrictions. -/
universe u v w t q
namespace CCO.ParityHasse.Relative
open Original
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) {i : ι}
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]
variable (H : HomogeneousSource S G)
variable (cco : SemanticCCO.{u,v,max u v,w} S)
variable {Q : Type q} [MulAction G Q]

noncomputable abbrev namedQuotient (π : X i → Q)
    (surjπ : Function.Surjective π)
    (equivπ : ∀ (g : G) x, π (g • x) = g • π x) :=
  RawExact.actualQuotientAtomicSource (fun _ : Unit => Q) S H
    (fun _ => π) (fun _ => surjπ) (fun _ => equivπ)

 theorem namedQuotient_atom (π : X i → Q) (surjπ : Function.Surjective π)
    (equivπ : ∀ (g : G) x, π (g • x) = g • π x) {j k : Unit}
    (a : (namedQuotient S H π surjπ equivπ).Atom j k) :
    (namedQuotient S H π surjπ equivπ).atomRel a = a.val := by
  funext x y; apply propext
  change RawExact.QuotientPalette.colour (fun _ : Unit => Q) x y = some a ↔ a.val x y
  apply (RawExact.QuotientPalette.colour_some_iff (G := G) (fun _ : Unit => Q) x y a).trans
  constructor
  · intro h; rw [h]; exact GroupActions.orbital_nonempty x y
  · intro h
    obtain ⟨q,r,hr⟩ := a.property.1
    rw [hr] at h ⊢
    exact (GroupActions.orbital_eq_of_mem q r x y h)

 theorem namedQuotient_word (π : X i → Q) (surjπ : Function.Surjective π)
    (equivπ : ∀ (g : G) x, π (g • x) = g • π x) {j k : Unit}
    (w : RawWord (namedQuotient S H π surjπ equivπ) j k) :
    ∃ o : OrbitalWord Q, OrbitalWord.relation G Q o =
      RawWord.relation (namedQuotient S H π surjπ equivπ) w := by
  induction w with
  | nil j => exact ⟨.nil,rfl⟩
  | identity tail ih => exact ih
  | atom a tail ih =>
    obtain ⟨o,ho⟩ := ih
    obtain ⟨x,y,ha⟩ := a.property.1
    refine ⟨.atom x y o,?_⟩
    change mul (GroupActions.orbital (G := G) x y) (OrbitalWord.relation G Q o) =
      mul ((namedQuotient S H π surjπ equivπ).atomRel a) (RawWord.relation _ tail)
    rw [ho,namedQuotient_atom S H π surjπ equivπ a,ha]

 theorem namedQuotient_presentation (π : X i → Q) (surjπ : Function.Surjective π)
    (equivπ : ∀ (g : G) x, π (g • x) = g • π x)
    (P : RawExact.Presentation (namedQuotient S H π surjπ equivπ) () ()) :
    ∃ O : List (OrbitalWord Q), orbitalEvaluate G Q O =
      RawExact.evaluate (namedQuotient S H π surjπ equivπ) P := by
  induction P with
  | nil =>
    refine ⟨[],?_⟩
    funext x y; apply propext
    simp [orbitalEvaluate,RawExact.evaluate]
  | cons w P ih =>
    obtain ⟨o,ho⟩ := namedQuotient_word S H π surjπ equivπ w
    obtain ⟨O,hO⟩ := ih
    refine ⟨o::O,?_⟩
    have ha (x y : Q) := congrFun (congrFun hO x) y
    funext x y; apply propext
    simp only [orbitalEvaluate,RawExact.evaluate,List.mem_cons,forall_eq_or_imp]
    rw [← ho]
    exact and_congr Iff.rfl (iff_of_eq (ha x y))

 theorem namedQuotient_exact_is_orbitalExact (π : X i → Q) (surjπ : Function.Surjective π)
    (equivπ : ∀ (g : G) x, π (g • x) = g • π x)
    (D : RawExact.NonemptyExact (namedQuotient S H π surjπ equivπ) () ()) :
    OrbitalExact G Q (RawExact.evaluate (namedQuotient S H π surjπ equivπ) D.words) := by
  obtain ⟨O,hO⟩ := namedQuotient_presentation S H π surjπ equivπ D.words
  exact ⟨O,hO,D.nonempty⟩

include H cco in
/-- Every FULL exact relation in the accepted actual named quotient API
has a full exact OLD pullback. This is not merely an abstract word model. -/
theorem namedQuotient_full_exact_pullback (π : X i → Q) (surjπ : Function.Surjective π)
    (equivπ : ∀ (g : G) x, π (g • x) = g • π x)
    (K : ColourEq S i) (hK : GroupActions.kernel π = K) (exK : Exact S K)
    (D : RawExact.NonemptyExact (namedQuotient S H π surjπ equivπ) () ()) :
    Exact S (pull π (RawExact.evaluate (namedQuotient S H π surjπ equivπ) D.words)) :=
  actual_quotient_exact_pullback S H cco π surjπ equivπ K hK exK _
    (namedQuotient_exact_is_orbitalExact S H π surjπ equivπ D)

include H in
/-- The distinguished quotient gate has a literal singleton-atom exact
presentation in the accepted actual quotient source. -/
theorem namedQuotient_gate_exact (Y U : ColourEq S i) (M : MaximalGate S H Y U)
    (π : X i → Q) (surjπ : Function.Surjective π)
    (equivπ : ∀ (g : G) x, π (g • x) = g • π x)
    (hK : GroupActions.kernel π = M.kernel) (q : Q) :
    ∃ D : RawExact.NonemptyExact (namedQuotient S H π surjπ equivπ) () (),
      RawExact.evaluate (namedQuotient S H π surjπ equivπ) D.words =
        imageRelation π (gate S M.kernel U Y) := by
  let I := quotientGateInvolution S H Y U M π surjπ hK
  have hne : (⟨(),q⟩ : Sigma (fun _ : Unit => Q)) ≠ ⟨(),I.map q⟩ := by
    intro heq
    have h : q = I.map q := by simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using heq
    exact I.fixedPointFree q h.symm
  let a := RawExact.QuotientPalette.pairAtom (G := G) (fun _ : Unit => Q) q (I.map q) hne
  refine ⟨RawExact.exactDiversityAtom (namedQuotient S H π surjπ equivπ) a,?_⟩
  calc
    RawExact.evaluate (namedQuotient S H π surjπ equivπ) (RawExact.exactDiversityAtom (namedQuotient S H π surjπ equivπ) a).words =
        (namedQuotient S H π surjπ equivπ).atomRel a := RawExact.exactDiversityAtom_relation (namedQuotient S H π surjπ equivπ) a
    _ = a.val := namedQuotient_atom S H π surjπ equivπ a
    _ = GroupActions.orbital (G := G) q (I.map q) := rfl
    _ = _ := (quotient_gate_actual_orbital S H Y U M π surjπ equivπ hK q).symm

include H cco in
/-- C26 with a literal accepted actual quotient RAW presentation for Z. -/
theorem namedQuotient_gate_dominance (Y U : ColourEq S i) (M : MaximalGate S H Y U)
    (π : X i → Q) (surjπ : Function.Surjective π)
    (equivπ : ∀ (g : G) x, π (g • x) = g • π x)
    (hK : GroupActions.kernel π = M.kernel)
    (Z : Setoid Q)
    (D : RawExact.NonemptyExact (namedQuotient S H π surjπ equivπ) () ())
    (hD : RawExact.evaluate (namedQuotient S H π surjπ equivπ) D.words = Z)
    (hZ : (⊥ : Setoid Q) < Z) :
    ∀ q r, imageRelation π (gate S M.kernel U Y) q r → Z q r := by
  apply quotient_gate_dominance S H cco Y U M π surjπ equivπ hK Z _ hZ
  rw [← hD]
  exact namedQuotient_exact_is_orbitalExact S H π surjπ equivπ D

end CCO.ParityHasse.Relative
