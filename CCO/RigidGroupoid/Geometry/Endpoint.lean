import CCO.RigidGroupoid.Geometry.Correspondence

/-! Standalone C16/C17 needs projected exactness ONLY at the TWO endpoints.
Other fine kernels occur in the quotient word language, but no coarse gate or
coarse projected-exactness assumption is made at those other named sorts. -/

universe u v w q r t
namespace CCO.RigidGroupoid.Geometry.Endpoint
open RawExact
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
variable {i j : ι} (A : Kernel S i) (B : Kernel S j)
variable (ha : ∀ x y, π i x = π i y → A.rel x y)
variable (hb : ∀ x y, π j x = π j y → B.rel x y)
variable (hAq : FullExact T (A.projectedSetoid (π i) (surjπ i) ha).r)
variable (hBq : FullExact T (B.projectedSetoid (π j) (surjπ j) hb).r)

private theorem pba :
    GroupActions.pullback (π i) (π i) (A.projectedKernel T (π i) (surjπ i) ha hAq).rel = A.rel :=
  A.projected_pullback (π i) (surjπ i) ha

private theorem pbb :
    GroupActions.pullback (π j) (π j) (B.projectedKernel T (π j) (surjπ j) hb hBq).rel = B.rel :=
  B.projected_pullback (π j) (surjπ j) hb

include surjπ in
private theorem pbcomp {a b c : ι} (D : TRel Q a b) (F : TRel Q b c) :
    GroupActions.pullback (π a) (π c) (TRel.comp D F) =
      TRel.comp (GroupActions.pullback (π a) (π b) D) (GroupActions.pullback (π b) (π c) F) :=
  ExactCRT.pullback_comp (π a) (π b) (π c) (surjπ b) D F

include H cco equivπ E hE hT surjπ ha hb hAq hBq
theorem forward_exact (R : Arrow S A B) : FullExact T (Quotient.image (π i) (π j) R.rel) := by
  obtain ⟨x,y,hxy⟩ := R.exact.nonempty S
  let Aq := A.projectedKernel T (π i) (surjπ i) ha hAq
  let Bq := B.projectedKernel T (π j) (surjπ j) hb hBq
  have hrect : Quotient.image (π i) (π j) R.rel =
      TRel.comp (TRel.comp Aq.rel (T.rawAtomRel (T.colour (π i x) (π j y)))) Bq.rel := by
    apply ExactCRT.pullback_injective (π i) (π j) (surjπ i) (surjπ j)
    rw [R.image_pullback_nested (π i) (π j) ha hb,pbcomp π surjπ,pbcomp π surjπ]
    have hpa : GroupActions.pullback (π i) (π i) Aq.rel = A.rel := A.projected_pullback (π i) (surjπ i) ha
    have hpb : GroupActions.pullback (π j) (π j) Bq.rel = B.rel := B.projected_pullback (π j) (surjπ j) hb
    rw [hpa,hpb,ExactCRT.quotient_pair_block S T H π equivπ E hE hT x y,R.rectangular H hxy]
    have hea : TRel.comp A.rel (evaluate S (E i).words) = A.rel := by
      rw [← hE i]
      exact A.right_kernel (π i) ha
    have heb : TRel.comp (evaluate S (E j).words) B.rel = B.rel := by
      rw [← hE j]
      exact B.left_kernel (π j) hb
    dsimp only [saturate]
    simp only [← TRel.comp_assoc]
    rw [hea,TRel.comp_assoc (TRel.comp A.rel (S.rawAtomRel (S.colour x y)))
      (evaluate S (E j).words) B.rel,heb]
  rw [hrect]
  let Cq := Quotient.quotientExactCalculus S T H cco π surjπ equivπ E hE hT
  exact Cq.comp (Cq.comp hAq (fullExact_actual_atom T (π i x) (π j y))) hBq

noncomputable def push (R : Arrow S A B) :
    Arrow T (A.projectedKernel T (π i) (surjπ i) ha hAq)
      (B.projectedKernel T (π j) (surjπ j) hb hBq) where
  rel := Quotient.image (π i) (π j) R.rel
  exact := forward_exact S T H cco π surjπ equivπ E hE hT A B ha hb hAq hBq R
  left := by
    apply ExactCRT.pullback_injective (π i) (π j) (surjπ i) (surjπ j)
    rw [pbcomp π surjπ,pba,
      R.image_pullback_nested (π i) (π j) ha hb,R.left]
  right := by
    apply ExactCRT.pullback_injective (π i) (π j) (surjπ i) (surjπ j)
    rw [pbcomp π surjπ,pbb,
      R.image_pullback_nested (π i) (π j) ha hb,R.right]
  source := by
    apply ExactCRT.pullback_injective (π i) (π i) (surjπ i) (surjπ i)
    rw [pbcomp π surjπ,pba]
    change TRel.comp _ (TRel.converse (GroupActions.pullback (π i) (π j)
      (Quotient.image (π i) (π j) R.rel))) = _
    rw [R.image_pullback_nested (π i) (π j) ha hb,R.source]
  target := by
    apply ExactCRT.pullback_injective (π j) (π j) (surjπ j) (surjπ j)
    rw [pbcomp π surjπ,pbb]
    change TRel.comp (TRel.converse (GroupActions.pullback (π i) (π j)
      (Quotient.image (π i) (π j) R.rel))) _ = _
    rw [R.image_pullback_nested (π i) (π j) ha hb,R.target]

noncomputable def pull
    (R : Arrow T (A.projectedKernel T (π i) (surjπ i) ha hAq)
      (B.projectedKernel T (π j) (surjπ j) hb hBq)) : Arrow S A B where
  rel := GroupActions.pullback (π i) (π j) R.rel
  exact := Quotient.fullExactPullback S T H cco π surjπ equivπ E hE hT R.exact
  left := by
    have h := congrArg (GroupActions.pullback (π i) (π j)) R.left
    rw [pbcomp π surjπ,pba] at h
    exact h
  right := by
    have h := congrArg (GroupActions.pullback (π i) (π j)) R.right
    rw [pbcomp π surjπ,pbb] at h
    exact h
  source := by
    have h := congrArg (GroupActions.pullback (π i) (π i)) R.source
    rw [pbcomp π surjπ,pba] at h
    exact h
  target := by
    have h := congrArg (GroupActions.pullback (π j) (π j)) R.target
    rw [pbcomp π surjπ,pbb] at h
    exact h

noncomputable def arrowEquiv : Arrow S A B ≃
    Arrow T (A.projectedKernel T (π i) (surjπ i) ha hAq)
      (B.projectedKernel T (π j) (surjπ j) hb hBq) where
  toFun := push S T H cco π surjπ equivπ E hE hT A B ha hb hAq hBq
  invFun := pull S T H cco π surjπ equivπ E hE hT A B ha hb hAq hBq
  left_inv R := Arrow.ext (R.image_pullback_nested (π i) (π j) ha hb)
  right_inv R := Arrow.ext (Quotient.image_pullback (π i) (π j) (surjπ i) (surjπ j) R.rel)

end CCO.RigidGroupoid.Geometry.Endpoint
