import CCO.RawExact.JointLiftingSource

/-!
# Finite realignment of the constructed original automorphism

A back-and-forth limit need not lie in an arbitrary witness group G.
After that limit has been constructed, original finite homogeneity can
align its finitely many chosen original representatives by a genuine
member of G. Consequently every finite displayed joint map also has a
G-witness. This uses no closure or section hypothesis.
-/

universe u v w z t q

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Original finite homogeneity realigns any actual source automorphism
on a finite tuple of original real points. -/
theorem finite_original_realignment
    {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G) (g : OriginalAutomorphism S)
    {I : Type z} [Finite I]
    (sort : I → ι) (points : ∀ i, X (sort i)) :
    ∃ h : G, ∀ i, h • points i = g.equiv (sort i) (points i) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let e := Fintype.equivFin I
  let V := ULift.{max u v} (Fin (Fintype.card I))
  let source : V → Sigma X := fun i =>
    ⟨sort (e.symm i.down), points (e.symm i.down)⟩
  let target : V → Sigma X := fun i =>
    ⟨sort (e.symm i.down), g.equiv (sort (e.symm i.down)) (points (e.symm i.down))⟩
  have hColour : ∀ i j : V,
      taggedColour S (source i) (source j) = taggedColour S (target i) (target j) := by
    intro i j
    simp only [source, target, taggedColour, g.preserves_colours]
  obtain ⟨h, hh⟩ := H.extends_finite_diagram source target hColour
  refine ⟨h, ?_⟩
  intro i
  obtain ⟨n, rfl⟩ := e.symm.surjective i
  have htag := hh (ULift.up n)
  change (⟨sort (e.symm n), h • points (e.symm n)⟩ : Sigma X) =
    ⟨sort (e.symm n), g.equiv (sort (e.symm n)) (points (e.symm n))⟩ at htag
  simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using htag

/-- Finitely many actual quotient values of one original automorphism
can be realigned by a genuine G-element on their chosen representatives.
The real representatives are auxiliary witnesses, not new finite-domain
parameters and not a functorial section. -/
theorem finite_quotient_realignment
    {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G) (g : OriginalAutomorphism S)
    {K : Type z} (Q : K → Type q) [∀ k, MulAction G (Q k)]
    (root : K → ι) (π : ∀ k, X (root k) → Q k)
    (ontoπ : ∀ k, Function.Surjective (π k))
    (equivπ : ∀ k (h : G) c, π k (h • c) = h • π k c)
    (lift : ∀ k, Q k → Q k)
    (hLift : ∀ k x, lift k (π k x) = π k (g.equiv (root k) x))
    {I : Type*} [Finite I]
    (sort : I → K) (points : ∀ i, Q (sort i)) :
    ∃ h : G, ∀ i, h • points i = lift (sort i) (points i) := by
  classical
  let representatives : ∀ i, X (root (sort i)) :=
    fun i => (ontoπ (sort i) (points i)).choose
  have hRep : ∀ i, π (sort i) (representatives i) = points i :=
    fun i => (ontoπ (sort i) (points i)).choose_spec
  obtain ⟨h, hh⟩ := finite_original_realignment S H g
    (fun i => root (sort i)) representatives
  refine ⟨h, ?_⟩
  intro i
  calc
    h • points i = h • π (sort i) (representatives i) :=
      congrArg (fun a => h • a) (hRep i).symm
    _ = π (sort i) (h • representatives i) :=
      (equivπ (sort i) h (representatives i)).symm
    _ = π (sort i) (g.equiv (root (sort i)) (representatives i)) :=
      congrArg (π (sort i)) (hh i)
    _ = lift (sort i) (π (sort i) (representatives i)) :=
      (hLift (sort i) (representatives i)).symm
    _ = lift (sort i) (points i) := congrArg (lift (sort i)) (hRep i)

/-- The actual C21 source lift yields a genuine member of the original
finite-orbit witness group on the INITIAL FINITE joint domain. This is
proved by finite realignment; the countable limit itself is not declared
to lie in G. -/
theorem finite_joint_group_lifting_of_CCO
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
    ∃ h : G, ∀ p ∈ f.domain, h • p.2 = f.send p := by
  classical
  obtain ⟨g, q, hπ, hPair, hExt⟩ := actual_joint_lifting_of_CCO S H cco
    Q root π ontoπ equivπ E hE f
  have hOnto : ∀ k, Function.Surjective (jointProjection root π k) := by
    intro k
    cases k with
    | inl i => exact Function.surjective_id
    | inr j => exact ontoπ j
  have hEquiv : ∀ k (h : G) c,
      jointProjection root π k (h • c) = h • jointProjection root π k c := by
    intro k
    cases k with
    | inl i => exact fun _ _ => rfl
    | inr j => exact equivπ j
  have hLift : ∀ k x,
      jointEquiv g.equiv q k (jointProjection root π k x) =
        jointProjection root π k (g.equiv (jointRoot root k) x) := by
    intro k
    cases k with
    | inl i => exact fun _ => rfl
    | inr j => exact hπ j
  obtain ⟨h, hh⟩ := finite_quotient_realignment S H g
    (JointFamily X Q) (jointRoot root) (jointProjection root π)
    hOnto hEquiv (fun k => jointEquiv g.equiv q k) hLift
    (fun p : ↥f.domain => p.val.1) (fun p => p.val.2)
  refine ⟨h, ?_⟩
  intro p hp
  exact (hh ⟨p, hp⟩).trans (hExt p hp)

end CCO.RawExact
