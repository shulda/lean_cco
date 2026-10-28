import CCO.RawExact.JointCountableExtension

/-!
# One actual original automorphism induces the joint quotient map

Original real sorts are included explicitly as the identity quotients.
Back-and-forth produces sortwise bijections of the joint structure.
Its restriction to the real slots preserves the actual original binary
colouring, hence is an original automorphism. The mixed same-point
orbital proves that every quotient bijection is induced by this SAME
original automorphism, on every class, not only the displayed anchors.
-/

universe u v w z t

namespace CCO.RawExact

/-- A genuine automorphism of the original complete typed binary source.
The witness group used for finite orbital transport need not be closed
under countable back-and-forth limits. -/
structure OriginalAutomorphism {ι : Type u} {X : ι → Type v}
    (S : AtomicSource.{u,v,w} ι X) where
  equiv : ∀ i, X i ≃ X i
  preserves_colours : ∀ (i j : ι) (x : X i) (y : X j),
    S.colour (equiv i x) (equiv j y) = S.colour x y

/-- Literal real slots together with the displayed actual quotient slots.
The real slot at i is the identity quotient of X i. -/
def JointFamily {ι : Type u} (X : ι → Type v) {J : Type z}
    (Q : J → Type v) : ι ⊕ J → Type v
  | .inl i => X i
  | .inr j => Q j

instance JointFamily.mulAction {G : Type t} [Group G]
    {ι : Type u} {X : ι → Type v} {J : Type z} {Q : J → Type v}
    [∀ i, MulAction G (X i)] [∀ j, MulAction G (Q j)]
    (k : ι ⊕ J) : MulAction G (JointFamily X Q k) := by
  cases k <;> dsimp [JointFamily] <;> infer_instance

def jointRoot {ι : Type u} {J : Type z} (root : J → ι) : ι ⊕ J → ι :=
  Sum.elim id root

def jointProjection {ι : Type u} {X : ι → Type v}
    {J : Type z} {Q : J → Type v} (root : J → ι)
    (π : ∀ j, X (root j) → Q j) :
    ∀ k, X (jointRoot root k) → JointFamily X Q k
  | .inl _ => id
  | .inr j => π j

def jointEquiv {ι : Type u} {X : ι → Type v}
    {J : Type z} {Q : J → Type v}
    (g : ∀ i, X i ≃ X i) (q : ∀ j, Q j ≃ Q j) :
    ∀ k, JointFamily X Q k ≃ JointFamily X Q k
  | .inl i => g i
  | .inr j => q j

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- C21 actual typed joint lifting, conditional only on C13. All
quotient maps are actual equivariant surjections with full-exact
kernels. The result is ONE original source automorphism inducing the
entire finite map on all displayed real and exact quotient sorts.
No closure of the named witness group, SAP or section is assumed. -/
theorem actual_joint_lifting_of_exact_ball_helly
    {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
    [∀ i, Countable (X i)]
    (H : HomogeneousSource S G)
    (hHelly : HeterogeneousExactBallHelly S)
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
      (∀ p ∈ f.domain, jointEquiv g.equiv q p.1 p.2 = f.send p) := by
  classical
  let : Fintype ι := S.finiteSort
  let : Encodable ι := Encodable.ofCountable _
  let : Encodable J := Encodable.ofCountable _
  let : ∀ k : ι ⊕ J, Encodable (JointFamily X Q k) := by
    intro k
    cases k with
    | inl i => exact Encodable.ofCountable (X i)
    | inr j =>
        let : Countable (Q j) := (ontoπ j).countable
        exact Encodable.ofCountable (Q j)
  have : Countable (Sigma (JointFamily X Q)) := inferInstance
  let K : ∀ k, NonemptyExact S (jointRoot root k) (jointRoot root k) := by
    intro k
    cases k with
    | inl i => exact exactIdentityAtom S i
    | inr j => exact E j
  have hK : ∀ k,
      GroupActions.kernel (jointProjection root π k) = evaluate S (K k).words := by
    intro k
    cases k with
    | inl i =>
        change GroupActions.kernel (fun x : X i => x) =
          evaluate S (exactIdentityAtom S i).words
        rw [exactIdentityAtom_relation S i]
        rfl
    | inr j => exact hE j
  have hOnto : ∀ k, Function.Surjective (jointProjection root π k) := by
    intro k
    cases k with
    | inl i => exact Function.surjective_id
    | inr j => exact ontoπ j
  have hEquiv : ∀ k (g : G) c,
      jointProjection root π k (g • c) = g • jointProjection root π k c := by
    intro k
    cases k with
    | inl i => exact fun _ _ => rfl
    | inr j => exact equivπ j
  obtain ⟨e, hePair, heExt⟩ := countable_joint_extension_of_exact_ball_helly S H hHelly
    (JointFamily X Q) (jointRoot root) (jointProjection root π)
    hOnto hEquiv K hK f
  let real : ∀ i, X i ≃ X i := fun i => e (.inl i)
  let quotient : ∀ j, Q j ≃ Q j := fun j => e (.inr j)
  have hColour : ∀ (i j : ι) (x : X i) (y : X j),
      S.colour (real i x) (real j y) = S.colour x y := by
    intro i j x y
    obtain ⟨g, hgx, hgy⟩ := hePair (.inl i) (.inl j) x y
    have hgx' : g • x = real i x := hgx
    have hgy' : g • y = real j y := hgy
    have h := S.colourInvariant_of_homogeneous H g x y
    rw [hgx', hgy'] at h
    exact h
  let g : OriginalAutomorphism S := ⟨real, hColour⟩
  have hJoint : jointEquiv g.equiv quotient = e := by
    funext k
    cases k <;> rfl
  refine ⟨g, quotient, ?_, ?_, ?_⟩
  · intro j x
    obtain ⟨h, hhx, hhq⟩ := hePair (.inl (root j)) (.inr j) x (π j x)
    calc
      quotient j (π j x) = h • π j x := hhq.symm
      _ = π j (h • x) := (equivπ j h x).symm
      _ = π j (g.equiv (root j) x) := congrArg (π j) hhx
  · simpa only [hJoint] using hePair
  · intro p hp
    cases p with
    | mk k p =>
      cases k with
      | inl i => exact heExt ⟨.inl i, p⟩ hp
      | inr j => exact heExt ⟨.inr j, p⟩ hp

end CCO.RawExact
