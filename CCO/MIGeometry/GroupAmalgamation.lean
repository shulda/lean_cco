import CCO.AclOwners.ClosedAmalgamation

/-! Finite induced embeddings in the original homogeneous source have
individual group extensions. Aligning the left extension gives a literal
fixed-base group form of closed strong amalgamation. -/
universe v w t
namespace CCO.MIGeometry
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds AclOwners
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
include H

/-- Only one finite map is extended; no quotient global section is used. -/
theorem real_embedding_extension (L : Finset M) (f : RealInducedEmbedding S L) :
    ∃ g : G, ∀ x ∈ L, g • x = f.map x := by
  let p : ↥L → Sigma (fun _ : Unit => M) := fun x => ⟨(),x.val⟩
  let q : ↥L → Sigma (fun _ : Unit => M) := fun x => ⟨(),f.map x.val⟩
  have hc : ∀ x y, taggedColour S (p x) (p y) = taggedColour S (q x) (q y) := by
    intro x y
    apply congrArg (fun c : FullColour S =>
      (⟨(),(),c⟩ : Σ i : Unit, Σ j : Unit, Option (S.Atom i j)))
    exact (f.colours x.val x.property y.val y.property).symm
  obtain ⟨g,hg⟩ := H.extends_finite_diagram p q hc
  refine ⟨g,?_⟩
  intro x hx
  exact eq_of_heq (Sigma.mk.inj (hg ⟨x,hx⟩)).2

/-- Strong closed amalgamation with the left side fixed pointwise and
one original group element acting on the right. -/
theorem strong_closed_group_amalgamation (safe : Set (Atom S))
    (amalgamate : StrongClosedAmalgamation S G safe)
    (A L R : Finset M) (hA : Closed G A) (hL : Closed G L) (hR : Closed G R)
    (hAL : A ⊆ L) (hAR : A ⊆ R) :
    ∃ g : G, (∀ a ∈ A, g • a = a) ∧
      (∀ x ∈ L, ∀ y ∈ R, x = g • y ↔ x = y ∧ x ∈ A) ∧
      (∀ x ∈ L, x ∉ A → ∀ y ∈ R, y ∉ A →
        ∃ c ∈ safe, col S x (g • y) = some c) := by
  obtain ⟨f,f',base,strong,cross⟩ := amalgamate A L R hA hL hR hAL hAR
  obtain ⟨l,hl⟩ := real_embedding_extension S H L f
  obtain ⟨r,hr⟩ := real_embedding_extension S H R f'
  refine ⟨l⁻¹ * r,?_,?_,?_⟩
  · intro a ha
    have he : r • a = l • a := (hr a (hAR ha)).trans
      ((base a ha).symm.trans (hl a (hAL ha)).symm)
    rw [mul_smul,he,inv_smul_smul]
  · intro x hx y hy
    have he : x = (l⁻¹ * r) • y ↔ f.map x = f'.map y := by
      rw [← hl x hx,← hr y hy,mul_smul,eq_inv_smul_iff]
    exact he.trans (strong x hx y hy)
  · intro x hx hxA y hy hyA
    obtain ⟨c,hc,hcol⟩ := cross x hx hxA y hy hyA
    refine ⟨c,hc,?_⟩
    have hc : col S (l • x) (r • y) = some c := by
      rw [hl x hx,hr y hy]
      exact hcol
    have hi : col S (l • x) (r • y) = col S x ((l⁻¹ * r) • y) := by
      simpa only [mul_smul,smul_inv_smul] using col_invariant S H l x ((l⁻¹ * r) • y)
    exact hi.symm.trans hc

/-- A global witness-group motion is a finite induced embedding. -/
def actionEmbedding (g : G) (L : Finset M) : RealInducedEmbedding S L where
  map := fun x => g • x
  injective := fun _ _ _ _ he => MulAction.injective g he
  colours := fun x _ y _ => col_invariant S H g x y

end CCO.MIGeometry
