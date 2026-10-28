import CCO.RawExact.ExactBallHellySource
import CCO.RawExact.EquivariantUnaryLifting

/-!
# C20–C23 from original semantic CCO and actual full-exact quotients

The true source C13 theorem discharges the only remaining Helly provider.
The countable limit is constructed as an actual original source
colour automorphism, with its induced quotient action proved globally.
-/

universe u v w z t r

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- C20 source theorem: extend an actual finite joint partial
isomorphism by a displayed actual quotient point. Original real points
are its identity-quotient special case. All providers are discharged. -/
theorem finite_joint_extension_of_CCO
    {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {K : Type z} (Q : K → Type r) [∀ k, MulAction G (Q k)]
    (root : K → ι) (π : ∀ k, X (root k) → Q k)
    (ontoπ : ∀ k, Function.Surjective (π k))
    (equivπ : ∀ k (g : G) c, π k (g • c) = g • π k c)
    (E : ∀ k, NonemptyExact S (root k) (root k))
    (hE : ∀ k, GroupActions.kernel (π k) = evaluate S (E k).words)
    (f : FiniteJointPartialIso G Q) (k : K) (x : X (root k)) :
    ∃ f' : FiniteJointPartialIso G Q,
      (∀ p, p ∈ f'.domain ↔ p = (⟨k, π k x⟩ : Sigma Q) ∨ p ∈ f.domain) ∧
      ∀ p ∈ f.domain, f'.send p = f.send p :=
  finite_joint_extension_of_exact_ball_helly S H
    (heterogeneousExactBallHelly_of_CCO S H cco)
    Q root π ontoπ equivπ E hE f k x

/-- C21 source theorem: one genuine original automorphism induces the
entire actual finite joint partial isomorphism. The actual quotient
projection equations hold on every original representative. -/
theorem actual_joint_lifting_of_CCO
    {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
    [∀ i, Countable (X i)]
    (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {J : Type z} [Finite J]
    (Q : J → Type v) [∀ j, MulAction G (Q j)]
    (root : J → ι) (π : ∀ j, X (root j) → Q j)
    (ontoπ : ∀ j, Function.Surjective (π j))
    (equivπ : ∀ j (g : G) c, π j (g • c) = g • π j c)
    (E : ∀ j, NonemptyExact S (root j) (root j))
    (hE : ∀ j, GroupActions.kernel (π j) = evaluate S (E j).words)
    (f : FiniteJointPartialIso G (JointFamily X Q)) :
    ∃ (g : OriginalAutomorphism S) (q : ∀ j, Q j ≃ Q j),
      (∀ j (x : X (root j)), q j (π j x) = π j (g.equiv (root j) x)) ∧
      (∀ (k l : ι ⊕ J) (a : JointFamily X Q k) (b : JointFamily X Q l),
        GroupActions.orbital (G := G) a b
          (jointEquiv g.equiv q k a) (jointEquiv g.equiv q l b)) ∧
      (∀ p ∈ f.domain, jointEquiv g.equiv q p.1 p.2 = f.send p) :=
  actual_joint_lifting_of_exact_ball_helly S H
    (heterogeneousExactBallHelly_of_CCO S H cco)
    Q root π ontoπ equivπ E hE f

/-- C22 source theorem: the same original lift preserves every actual
equivariant unary function. Forgetting unary symbols from a finite closed
partial isomorphism leaves exactly the binary finite domain used here. -/
theorem actual_joint_unary_lifting_of_CCO
    {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
    [∀ i, Countable (X i)]
    (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {J : Type z} [Finite J]
    (Q : J → Type v) [∀ j, MulAction G (Q j)]
    (root : J → ι) (π : ∀ j, X (root j) → Q j)
    (ontoπ : ∀ j, Function.Surjective (π j))
    (equivπ : ∀ j (g : G) c, π j (g • c) = g • π j c)
    (E : ∀ j, NonemptyExact S (root j) (root j))
    (hE : ∀ j, GroupActions.kernel (π j) = evaluate S (E j).words)
    (f : FiniteJointPartialIso G (JointFamily X Q))
    {T : Type r} (domainSort codomainSort : T → ι ⊕ J)
    (τ : ∀ t : T, JointFamily X Q (domainSort t) → JointFamily X Q (codomainSort t))
    (equivτ : ∀ t (h : G) a, τ t (h • a) = h • τ t a) :
    ∃ (g : OriginalAutomorphism S) (q : ∀ j, Q j ≃ Q j),
      (∀ j (x : X (root j)), q j (π j x) = π j (g.equiv (root j) x)) ∧
      (∀ p ∈ f.domain, jointEquiv g.equiv q p.1 p.2 = f.send p) ∧
      (∀ t a, jointEquiv g.equiv q (codomainSort t) (τ t a) =
        τ t (jointEquiv g.equiv q (domainSort t) a)) :=
  actual_joint_unary_lifting_of_exact_ball_helly S H
    (heterogeneousExactBallHelly_of_CCO S H cco)
    Q root π ontoπ equivπ E hE f domainSort codomainSort τ equivτ

/-- C23 is the genuine one-original-sort specialization. It lifts all
finite real and actual exact quotient requests simultaneously by ONE
original colour automorphism, with no SAP or coherent-section premise. -/
theorem one_sort_joint_lifting_of_CCO
    {A : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => A))
    {G : Type t} [Group G] [MulAction G A] [Countable A]
    (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,v,w} S)
    {J : Type z} [Finite J]
    (Q : J → Type v) [∀ j, MulAction G (Q j)]
    (π : ∀ j, A → Q j)
    (ontoπ : ∀ j, Function.Surjective (π j))
    (equivπ : ∀ j (g : G) c, π j (g • c) = g • π j c)
    (E : ∀ _ : J, NonemptyExact S () ())
    (hE : ∀ j, GroupActions.kernel (π j) = evaluate S (E j).words)
    (f : FiniteJointPartialIso G (JointFamily (fun _ : Unit => A) Q)) :
    ∃ (g : A ≃ A) (q : ∀ j, Q j ≃ Q j),
      (∀ x y, S.colour (i := ()) (j := ()) (g x) (g y) =
        S.colour (i := ()) (j := ()) x y) ∧
      (∀ j x, q j (π j x) = π j (g x)) ∧
      (∀ p ∈ f.domain, jointEquiv (fun _ : Unit => g) q p.1 p.2 = f.send p) := by
  obtain ⟨g, q, hπ, hPair, hExt⟩ := actual_joint_lifting_of_CCO S H cco
    Q (fun _ => ()) π ontoπ equivπ E hE f
  refine ⟨g.equiv (), q, ?_, hπ, ?_⟩
  · exact g.preserves_colours () ()
  · intro p hp
    cases p with
    | mk k p =>
      cases k with
      | inl i => cases i; exact hExt ⟨.inl (), p⟩ hp
      | inr j => exact hExt ⟨.inr j, p⟩ hp

end CCO.RawExact
