import CCO.RawExact.QuotientFiniteHomogeneity
import CCO.RawExact.QuotientAgeAP

/-!
# Actual quotient source homogeneity

The palette constructor must identify equality of its actual optional
colours with actual original-group pair orbitals. The proved finite
quotient tuple lifting theorem then supplies the whole finite-tuple
homogeneity interface, including repeated values and all named sorts.
-/

universe u v w z t r

namespace CCO.RawExact

private theorem sigma_cast_eq {K : Type z} {Q : K → Type v}
    (p q : Sigma Q) (h : q.1 = p.1) :
    (⟨p.1, h ▸ q.2⟩ : Sigma Q) = q := by
  cases p with
  | mk k x =>
    cases q with
    | mk l y =>
      change l = k at h
      cases h
      rfl

private theorem sigma_smul_eta {G : Type t} [Group G]
    {K : Type z} {Q : K → Type v} [∀ k, MulAction G (Q k)]
    (g : G) (p : Sigma Q) :
    g • p = (⟨p.1, g • p.2⟩ : Sigma Q) := by
  cases p
  rfl

private theorem orbital_of_tagged_colour_eq
    {G : Type t} [Group G] {K : Type z} {Q : K → Type v}
    [∀ k, MulAction G (Q k)]
    (P : AtomicSource.{z,v,r} K Q)
    (hColour : ∀ {k l} (x : Q k) (y : Q l) (x' : Q k) (y' : Q l),
      P.colour x y = P.colour x' y' ↔
        GroupActions.orbital (G := G) x y x' y')
    (p q p' q' : Sigma Q)
    (h : taggedColour P p q = taggedColour P p' q') :
    GroupActions.orbital (G := G) p q p' q' := by
  cases p with
  | mk k x =>
    cases q with
    | mk l y =>
      cases p' with
      | mk k' x' =>
        cases q' with
        | mk l' y' =>
          have hk : k = k' := congrArg Sigma.fst h
          cases hk
          have hl : l = l' :=
            congrArg (fun c : Σ k, Σ l, Option (P.Atom k l) => c.2.1) h
          cases hl
          have hc : P.colour x y = P.colour x' y' := by
            simpa only [taggedColour, Sigma.mk.injEq, heq_eq_eq, true_and] using h
          obtain ⟨g, hgx, hgy⟩ := (hColour x y x' y').mp hc
          exact ⟨g, congrArg (Sigma.mk k) hgx, congrArg (Sigma.mk l) hgy⟩

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- The actual quotient palette's source homogeneity, with genuine
source C13/C21 providers discharged. The colour-orbital equation is
proved by the actual palette constructor, not supplied as a new axiom. -/
theorem actual_quotient_homogeneous_of_CCO
    {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
    [∀ i, Countable (X i)]
    (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {K : Type z} [Finite K]
    (Q : K → Type v) [∀ k, MulAction G (Q k)]
    (root : K → ι) (π : ∀ k, X (root k) → Q k)
    (ontoπ : ∀ k, Function.Surjective (π k))
    (equivπ : ∀ k (g : G) c, π k (g • c) = g • π k c)
    (E : ∀ k, NonemptyExact S (root k) (root k))
    (hE : ∀ k, GroupActions.kernel (π k) = evaluate S (E k).words)
    (P : AtomicSource.{z,v,r} K Q)
    (hColour : ∀ {k l} (x : Q k) (y : Q l) (x' : Q k) (y' : Q l),
      P.colour x y = P.colour x' y' ↔
        GroupActions.orbital (G := G) x y x' y') :
    HomogeneousSource P G := by
  refine ⟨?_, ?_, ?_⟩
  · intro g p
    cases p
    rfl
  · intro g p q
    cases p with
    | mk k x =>
      cases q with
      | mk l y =>
        have hc : P.colour (g • x) (g • y) = P.colour x y :=
          ((hColour x y (g • x) (g • y)).mpr ⟨g, rfl, rfl⟩).symm
        change (⟨k, l, P.colour (g • x) (g • y)⟩ : Σ k, Σ l, Option (P.Atom k l)) =
          ⟨k, l, P.colour x y⟩
        rw [hc]
  · intro V _ source target hTagged
    have hSort : ∀ p, (target p).1 = (source p).1 := by
      intro p
      exact (congrArg Sigma.fst (hTagged p p)).symm
    let sort : V → K := fun p => (source p).1
    let left : ∀ p : V, Q (sort p) := fun p => (source p).2
    let right : ∀ p : V, Q (source p).1 := fun p => hSort p ▸ (target p).2
    have hRight : ∀ p : V, (⟨sort p, right p⟩ : Sigma Q) = target p :=
      fun p => sigma_cast_eq (source p) (target p) (hSort p)
    have hPair : ∀ p q : V, GroupActions.orbital (G := G)
        (left p) (left q) (right p) (right q) := by
      intro p q
      obtain ⟨g, hgp, hgq⟩ := orbital_of_tagged_colour_eq P hColour
        (source p) (source q) (target p) (target q) (hTagged p q)
      refine ⟨g, ?_, ?_⟩
      · have h := (sigma_smul_eta g (source p)).symm.trans (hgp.trans (hRight p).symm)
        simpa only [sort, left, Sigma.mk.injEq, heq_eq_eq, true_and] using h
      · have h := (sigma_smul_eta g (source q)).symm.trans (hgq.trans (hRight q).symm)
        simpa only [sort, left, Sigma.mk.injEq, heq_eq_eq, true_and] using h
    obtain ⟨g, hg⟩ := finite_quotient_tuple_lifting_of_CCO S H cco
      Q root π ontoπ equivπ E hE sort left right hPair
    refine ⟨g, ?_⟩
    intro p
    calc
      g • source p = (⟨sort p, g • left p⟩ : Sigma Q) := sigma_smul_eta g (source p)
      _ = ⟨sort p, right p⟩ := congrArg (Sigma.mk (sort p)) (hg p)
      _ = target p := hRight p

/-- C25 amalgamation for a representation of the actual quotient
orbital source. The actual palette constructor discharges its explicit
colour-orbital representation equation. Additional identifications in
the amalgam are permitted, as required for AP rather than SAP. -/
theorem quotient_ageAP_of_colour_orbitals
    {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
    [∀ i, Countable (X i)]
    (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {K : Type z} [Finite K]
    (Q : K → Type v) [∀ k, MulAction G (Q k)]
    (root : K → ι) (π : ∀ k, X (root k) → Q k)
    (ontoπ : ∀ k, Function.Surjective (π k))
    (equivπ : ∀ k (g : G) c, π k (g • c) = g • π k c)
    (E : ∀ k, NonemptyExact S (root k) (root k))
    (hE : ∀ k, GroupActions.kernel (π k) = evaluate S (E k).words)
    (P : AtomicSource.{z,v,r} K Q)
    (hColour : ∀ {k l} (x : Q k) (y : Q l) (x' : Q k) (y' : Q l),
      P.colour x y = P.colour x' y' ↔
        GroupActions.orbital (G := G) x y x' y') : AgeAP P :=
  ageAP_of_homogeneous P
    (actual_quotient_homogeneous_of_CCO S H cco Q root π ontoπ equivπ E hE P hColour)

end CCO.RawExact
