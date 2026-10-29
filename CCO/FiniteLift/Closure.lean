import CCO.FiniteLift.Kernel
import CCO.FiniteLift.ClosureOrbit
import Mathlib.Data.Set.Card

/-! B029 C02–C06. Finite real fibres and full quotient stabilizers are kept
separate. Each finite joint lift fixes EACH original parameter; no ambient
quotient automorphism section or global group surjectivity is assumed. -/

universe v w t
namespace CCO.FiniteLift
open RawExact Owners.Product
variable {A : Type v} {G : Type t} [Group G] [MulAction G A]
variable {S : AtomicSource.{0,v,w} Unit (fun _ => A)}
namespace ExactKernel
variable (K : ExactKernel S G)

theorem finite_fibre (finiteK : K.FiniteClasses) (q : K.Q) :
    {x : A | K.proj x = q}.Finite := by
  obtain ⟨a, rfl⟩ := K.onto q
  have he : {x : A | K.proj x = K.proj a} = {x : A | K.rel a x} := by
    ext x
    exact K.proj_eq x a |>.trans ⟨K.rel.symm, K.rel.symm⟩
  rw [he]
  exact finiteK a

theorem fullPreimage_finite (finiteK : K.FiniteClasses) (B : Set K.Q)
    (finiteB : B.Finite) : (K.proj ⁻¹' B).Finite := by
  have h := Set.Finite.biUnion finiteB (fun q _ => K.finite_fibre finiteK q)
  apply h.subset
  intro x hx
  exact Set.mem_iUnion.mpr ⟨K.proj x, Set.mem_iUnion.mpr ⟨hx, rfl⟩⟩

/-- An original motion gives an actual bijection of ENTIRE K classes. -/
def fibreEquiv (g : G) (q : K.Q) :
    {x : A // K.proj x = q} ≃ {x : A // K.proj x = g • q} where
  toFun x := ⟨g • x.val, by rw [K.proj_smul, x.property]⟩
  invFun y := ⟨g⁻¹ • y.val, by rw [K.proj_smul, y.property, inv_smul_smul]⟩
  left_inv x := Subtype.ext (inv_smul_smul g x.val)
  right_inv y := Subtype.ext (smul_inv_smul g y.val)

/-- C02: transitivity identifies every full fibre with the same positive
finite class, including K=Id and finite original sources. -/
theorem uniform_fibre_card (H : HomogeneousSource S G) (finiteK : K.FiniteClasses) :
    ∃ k : ℕ, 0 < k ∧ ∀ q : K.Q, Nat.card {x : A // K.proj x = q} = k := by
  let a : A := Classical.choice (S.nonemptySort ())
  let k := Nat.card {x : A // K.proj x = K.proj a}
  haveI : Finite {x : A // K.proj x = K.proj a} := (K.finite_fibre finiteK _).to_subtype
  haveI : Nonempty {x : A // K.proj x = K.proj a} := ⟨⟨a, rfl⟩⟩
  refine ⟨k, Nat.card_pos, ?_⟩
  intro q
  obtain ⟨b, rfl⟩ := K.onto q
  obtain ⟨g, hg⟩ := S.original_sort_transitive_of_homogeneous H () a b
  have he := Nat.card_congr (K.fibreEquiv g (K.proj a))
  rw [← K.proj_smul, hg] at he
  exact he.symm

/-- The actual mixed real/K orbital, including membership and diagonals,
depends only on the two K projections. -/
theorem real_quotient_orbital (H : HomogeneousSource S G)
    (a a' : A) (q q' : K.Q) :
    GroupActions.orbital (G := G) a q a' q' ↔
      GroupActions.orbital (G := G) (K.proj a) q (K.proj a') q' :=
  actual_nested_orbit_reduction_of_homogeneous S H (i := ()) id K.proj K.proj
    Function.surjective_id K.onto (fun _ _ => rfl) K.proj_smul K.proj_smul
    (fun _ => rfl) a a' q q'

private def TwoFamily (b : Bool) : Type v := if b then K.Q else A
private def twoProjection : ∀ b : Bool, A → K.TwoFamily b
  | false => id
  | true => K.proj

/-- C04–C05 finite joint request: real A is fixed POINTWISE, every named
parameter class is fixed, and the one further class follows the GIVEN full
quotient automorphism. Repeated quotient values are retained consistently. -/
theorem fixing_real_lift [Countable A]
    (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
    (B : Set A) (finiteB : B.Finite) (β : FullAut G K.Q)
    (hβ : ∀ a ∈ B, β.val (K.proj a) = K.proj a) (x : A) :
    ∃ g : G, (∀ a ∈ B, g • a = a) ∧ g • K.proj x = β.val (K.proj x) := by
  classical
  letI : Finite B := finiteB.to_subtype
  letI : ∀ b : Bool, MulAction G (K.TwoFamily b) := by
    intro b
    cases b <;> dsimp [TwoFamily] <;> infer_instance
  let π := K.twoProjection
  have ontoπ : ∀ b, Function.Surjective (π b) := by
    intro b
    cases b
    · exact Function.surjective_id
    · exact K.onto
  have equivπ : ∀ b (g : G) a, π b (g • a) = g • π b a := by
    intro b g a
    cases b
    · rfl
    · exact K.proj_smul g a
  let E : ∀ _ : Bool, NonemptyExact S () ()
    | false => exactIdentityAtom S ()
    | true => K.exact
  have hE : ∀ b, GroupActions.kernel (π b) = evaluate S (E b).words := by
    intro b
    cases b
    · change GroupActions.kernel (id : A → A) = evaluate S (exactIdentityAtom S ()).words
      rw [exactIdentityAtom_relation S ()]
      rfl
    · exact K.kernel
  let I := B ⊕ (B ⊕ Unit)
  let sort : I → Bool
    | .inl _ => false
    | .inr _ => true
  let src : ∀ i : I, K.TwoFamily (sort i)
    | .inl a => a.val
    | .inr (.inl a) => K.proj a.val
    | .inr (.inr _) => K.proj x
  let dst : ∀ i : I, K.TwoFamily (sort i)
    | .inl a => a.val
    | .inr (.inl a) => β.val (K.proj a.val)
    | .inr (.inr _) => β.val (K.proj x)
  have mixed (a : B) (q : K.Q) :
      GroupActions.orbital (G := G) a.val q a.val (β.val q) := by
    apply (K.real_quotient_orbital H a.val a.val q (β.val q)).mpr
    have hh := orbitalAut_pair β (K.proj a.val) q
    change GroupActions.orbital (G := G) (K.proj a.val) q (β.val (K.proj a.val)) (β.val q) at hh
    rw [hβ a.val a.property] at hh
    exact hh
  have hp : ∀ i j : I, GroupActions.orbital (G := G) (src i) (src j) (dst i) (dst j) := by
    intro i j
    cases i with
    | inl a =>
      cases j with
      | inl b => exact GroupActions.orbital_nonempty _ _
      | inr j => cases j with
        | inl b => exact mixed a (K.proj b.val)
        | inr _ => exact mixed a (K.proj x)
    | inr i =>
      cases j with
      | inl a =>
        cases i with
        | inl b => obtain ⟨g, hg, hg'⟩ := mixed a (K.proj b.val); exact ⟨g, hg', hg⟩
        | inr _ => obtain ⟨g, hg, hg'⟩ := mixed a (K.proj x); exact ⟨g, hg', hg⟩
      | inr j =>
        cases i <;> cases j <;> exact orbitalAut_pair β _ _
  obtain ⟨g, hg⟩ := finite_quotient_tuple_lifting_of_CCO S H cco
    (K.TwoFamily) (fun _ => ()) π ontoπ equivπ E hE sort src dst hp
  refine ⟨g, ?_, ?_⟩
  · intro a ha
    exact hg (.inl (⟨a, ha⟩ : B))
  · exact hg (.inr (.inr ()))

/-- The image of the original pointwise stabilizer orbit is EXACTLY the
full quotient stabilizer orbit. This equality is proved by separately
chosen FINITE joint lifts; it asserts no group map onto full Aut(Q/K). -/
theorem projected_orbit_eq [Countable A]
    (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
    (B : Set A) (finiteB : B.Finite) (x : A) :
    K.proj '' orbitSet G B x = orbitSet (FullAut G K.Q) (K.proj '' B) (K.proj x) := by
  ext q
  constructor
  · rintro ⟨y, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨ambientAut (A := K.Q) g, ?_, ?_⟩
    · rintro c ⟨a, ha, rfl⟩
      change g • K.proj a = K.proj a
      rw [← K.proj_smul, hg a ha]
    · exact (K.proj_smul g x).symm
  · rintro ⟨β, hβ, hβq⟩
    obtain ⟨g, hg, hgx⟩ := K.fixing_real_lift H cco B finiteB β
      (fun a ha => hβ (K.proj a) ⟨a, ha, rfl⟩) x
    refine ⟨g • x, ⟨g, hg, rfl⟩, ?_⟩
    exact (K.proj_smul g x).trans (hgx.trans hβq)

/-- C06: both closure directions, including the empty finite base, with
FULL quotient stabilizers and no safe, witness, owner, normalization or EPPA input. -/
theorem acl_pullback [Countable A]
    (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
    (finiteK : K.FiniteClasses) (B : Set A) (finiteB : B.Finite) :
    aclSet G B = K.proj ⁻¹' aclSet (FullAut G K.Q) (K.proj '' B) := by
  ext x
  constructor
  · intro hx
    change (orbitSet (FullAut G K.Q) (K.proj '' B) (K.proj x)).Finite
    rw [← K.projected_orbit_eq H cco B finiteB x]
    exact hx.image K.proj
  · intro hx
    change (orbitSet G B x).Finite
    have hfin := K.fullPreimage_finite finiteK
      (orbitSet (FullAut G K.Q) (K.proj '' B) (K.proj x)) hx
    apply hfin.subset
    intro y hy
    have hh : K.proj y ∈ K.proj '' orbitSet G B x := ⟨y, hy, rfl⟩
    rwa [K.projected_orbit_eq H cco B finiteB x] at hh

/-- The cardinality of a full finite inverse image is the common fibre size
TIMES the number of distinct quotient classes; the empty case is retained. -/
theorem fullPreimage_card (finiteK : K.FiniteClasses) (B : Set K.Q)
    (finiteB : B.Finite) (k : ℕ)
    (hk : ∀ q : K.Q, Nat.card {x : A // K.proj x = q} = k) :
    Nat.card (K.proj ⁻¹' B) = k * Nat.card B := by
  classical
  letI : Fintype B := finiteB.fintype
  letI : ∀ q : B, Finite {x : A // K.proj x = q.val} :=
    fun q => (K.finite_fibre finiteK q.val).to_subtype
  let e : (K.proj ⁻¹' B) ≃ Σ q : B, {x : A // K.proj x = q.val} := {
    toFun := fun x => ⟨⟨K.proj x.val, x.property⟩, ⟨x.val, rfl⟩⟩
    invFun := fun q => ⟨q.2.val, by change K.proj q.2.val ∈ B; rw [q.2.property]; exact q.1.property⟩
    left_inv := fun _ => rfl
    right_inv := by rintro ⟨⟨q, hq⟩, x, hx⟩; cases hx; rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  simp only [hk, Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul,
    Nat.card_eq_fintype_card]
  exact Nat.mul_comm _ _

/-- Absolute closedness is preserved by full finite inverse image. No
claim that an arbitrary witness containing the input closure is closed. -/
theorem fullPreimage_closed [Countable A]
    (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
    (finiteK : K.FiniteClasses) (B : Set K.Q) (finiteB : B.Finite)
    (closedB : aclSet (FullAut G K.Q) B = B) :
    aclSet G (K.proj ⁻¹' B) = K.proj ⁻¹' B := by
  rw [K.acl_pullback H cco finiteK _ (K.fullPreimage_finite finiteK B finiteB)]
  rw [Set.image_preimage_eq B K.onto, closedB]

/-- The FULL quotient closure of every finite quotient base is finite.
It follows through the exact identity from the finite original closure,
rather than identifying full quotient automorphisms with the old image. -/
theorem quotient_acl_finite [Countable A]
    (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
    (finiteK : K.FiniteClasses) (B : Set K.Q) (finiteB : B.Finite) :
    (aclSet (FullAut G K.Q) B).Finite := by
  have hh := (aclSet_finite G S H (K.proj ⁻¹' B)
    (K.fullPreimage_finite finiteK B finiteB)).image K.proj
  rw [K.acl_pullback H cco finiteK _ (K.fullPreimage_finite finiteK B finiteB),
    Set.image_preimage_eq B K.onto, Set.image_preimage_eq _ K.onto] at hh
  exact hh

end ExactKernel
end CCO.FiniteLift
