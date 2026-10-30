import CCO.RankInduction.Basis
import CCO.RankInduction.FullPalette

/-! A rooted witness gives ordinary EPPA on that SAME finite carrier.
The empty input is handled separately and imposes no selected-root task. -/

namespace CCO.RankInduction
noncomputable section
open RawExact Owners.Product Owners.Provider

variable {G A U V : Type*} [Group G] [MulAction G A]
variable {ι : U → A} {κ : V → A}

def pushDomainLift (e : U ↪ V) (p : OrbitalPartial (G := G) ι)
    (x : e '' p.domain) : p.domain :=
  ⟨Classical.choose x.property,(Classical.choose_spec x.property).1⟩

theorem pushDomainLift_projection (e : U ↪ V) (p : OrbitalPartial (G := G) ι)
    (x : e '' p.domain) : e (pushDomainLift e p x).val = x.val :=
  (Classical.choose_spec x.property).2

def pushPartial (e : U ↪ V) (he : ∀ u, κ (e u) = ι u)
    (p : OrbitalPartial (G := G) ι) : OrbitalPartial (G := G) κ where
  domain := e '' p.domain
  map x := e (p.map (pushDomainLift e p x))
  injective := by
    intro x y hxy
    have hh := p.injective (e.injective hxy)
    apply Subtype.ext
    rw [← pushDomainLift_projection e p x,← pushDomainLift_projection e p y]
    exact congrArg (fun z : p.domain => e z.val) hh
  pair x y := by
    rw [← pushDomainLift_projection e p x,← pushDomainLift_projection e p y]
    simp only [he]
    exact p.pair (pushDomainLift e p x) (pushDomainLift e p y)

theorem pushPartial_at (e : U ↪ V) (he : ∀ u, κ (e u) = ι u)
    (p : OrbitalPartial (G := G) ι) (x : p.domain) :
    (pushPartial e he p).map ⟨e x.val,⟨x.val,x.property,rfl⟩⟩ = e (p.map x) := by
  apply congrArg e
  apply congrArg p.map
  apply Subtype.ext
  apply e.injective
  exact pushDomainLift_projection e p _

theorem eppaFromWitness {M : Type*} [MulAction G M]
    (S : AtomicSource Unit (fun _ => M)) (safe : Set (S.Atom () ()))
    (A0 W : Set M) (w : Witness S G safe A0 W) :
    ∃ e : A0 ↪ W,
      (∀ x y : A0, GroupActions.orbital (G := G) x.val y.val (e x).val (e y).val) ∧
      ∀ p : OrbitalPartial (G := G) (Subtype.val : A0 → M),
        ∃ β : OrbitalAut G M (Subtype.val : W → M),
          ∀ x : p.domain, β.val (e x.val) = e (p.map x) := by
  let inc : A0 ⊆ W := (FiniteLift.subset_aclSet G A0).trans w.closure
  let e : A0 ↪ W := Set.embeddingOfSubset A0 W inc
  have he : ∀ x, (e x).val = x.val := fun _ => rfl
  refine ⟨e,fun _ _ => ⟨1,one_smul _ _,one_smul _ _⟩,?_⟩
  intro p
  let q := pushPartial e he p
  have dom : q.domain ⊆ {x | x.val ∈ A0} := by
    rintro x ⟨a,ha,rfl⟩
    exact a.property
  have ran : ∀ x, q.map x ∈ {x | x.val ∈ A0} := by
    intro x
    exact (p.map (pushDomainLift e p x)).property
  obtain ⟨β,hβ⟩ := w.extensions q dom ran
  refine ⟨β,?_⟩
  intro x
  exact (hβ ⟨e x.val,⟨x.val,x.property,rfl⟩⟩).trans (pushPartial_at e he p x)

theorem ordinary_from_rooted {M : Type*} [MulAction G M]
    (S : AtomicSource Unit (fun _ => M)) (H : HomogeneousSource S G)
    (rooted : Rooted S G) : OrdinaryEPPA G M := by
  intro A0 finiteA
  by_cases nonemptyA : A0.Nonempty
  · obtain ⟨W,hW⟩ := rooted Set.univ (full_palette_strong_closed_amalgamation S H)
      A0 finiteA nonemptyA
    obtain ⟨e,pair,extensions⟩ := eppaFromWitness S Set.univ A0 W hW
    exact ⟨W,hW.finite,e,pair,extensions⟩
  · have he : A0 = ∅ := Set.not_nonempty_iff_eq_empty.mp nonemptyA
    subst A0
    refine ⟨∅,Set.finite_empty,Function.Embedding.refl _,?_,?_⟩
    · intro x
      exact False.elim x.property
    · intro p
      exact ⟨1,fun x => False.elim x.val.property⟩

end
end CCO.RankInduction
