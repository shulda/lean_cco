import CCO.RigidGroupoid.Geometry.Transport
import CCO.RigidGroupoid.Geometry.ProjectedKernels
import CCO.RigidGroupoid.Geometry.Quotient.Blocks

/-! Quotient dominance uses ONLY upward full exact word pullback. In the
coarse quotient by the arrow's actual gate, the arrow is one named actual
quotient orbital. Nonidentity makes this orbital a diversity letter. -/

universe u v w q r t
namespace CCO.RigidGroupoid.Geometry
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

include H cco equivπ E hE hT surjπ

theorem quotient_dominant {i : ι} (B : Kernel S i) (t : Arrow S B B)
    (hd : Dominant B t) (hK : GroupActions.kernel (π i) = B.rel)
    (Z : Setoid (Q i)) (hZ : FullExact T Z.r) (hne : Z ≠ ⊥) :
    ∀ x y, Quotient.image (π i) (π i) t.rel x y → Z x y := by
  let W : Kernel S i := ⟨Setoid.comap (π i) Z,
    Quotient.fullExactPullback S T H cco π surjπ equivπ E hE hT hZ⟩
  have hle : B ≤ W := by
    intro x y hxy
    have he : π i x = π i y := by
      change B.rel x y at hxy
      rw [← hK] at hxy
      exact hxy
    change Z (π i x) (π i y)
    simpa only [he] using Z.refl (π i y)
  have hstrict : B < W := by
    refine lt_iff_le_and_ne.mpr ⟨hle,?_⟩
    intro he
    apply hne
    apply Setoid.ext
    intro x y
    obtain ⟨a,rfl⟩ := surjπ i x
    obtain ⟨b,rfl⟩ := surjπ i y
    have hr : B.rel a b = W.rel a b := congrFun (congrFun (congrArg Kernel.rel he) a) b
    have hk : B.rel a b ↔ π i a = π i b :=
      (congrFun (congrFun hK a) b).symm.to_iff
    exact hr.symm.to_iff.trans hk
  rintro x y ⟨a,b,rfl,rfl,hab⟩
  exact hd W hstrict a b hab

omit cco in
theorem coarse_image_atom {i : ι} (B : Kernel S i) (R : Arrow S B B)
    (hK : GroupActions.kernel (π i) = B.rel) {x y : X i} (hxy : R.rel x y) :
    Quotient.image (π i) (π i) R.rel = T.rawAtomRel (T.colour (π i x) (π i y)) := by
  have hn : ∀ a b, π i a = π i b → B.rel a b := by
    intro a b hab
    rw [← hK]
    exact hab
  apply ExactCRT.pullback_injective (π i) (π i) (surjπ i) (surjπ i)
  rw [R.image_pullback_nested (π i) (π i) hn hn,
    ExactCRT.quotient_pair_block S T H π equivπ E hE hT x y,
    ← hE i,hK,← R.rectangular H hxy]

omit cco in
theorem coarse_nonidentity_diversity {i : ι} (B : Kernel S i) (R : Arrow S B B)
    (hK : GroupActions.kernel (π i) = B.rel) (hne : R ≠ Arrow.id B) :
    ∃ a : T.Atom i i, Quotient.image (π i) (π i) R.rel = T.atomRel a := by
  obtain ⟨x,y,hxy⟩ := R.exact.nonempty S
  have hatom := coarse_image_atom S T H π surjπ equivπ E hE hT B R hK hxy
  cases hc : T.colour (π i x) (π i y) with
  | some a =>
    refine ⟨a,hatom.trans ?_⟩
    rw [hc]
    rfl
  | none =>
    exfalso
    apply hne
    apply Arrow.ext
    have hn : ∀ a b, π i a = π i b → B.rel a b := by
      intro a b hab
      rw [← hK]
      exact hab
    have hi : T.rawAtomRel (none : Option (T.Atom i i)) = TRel.ident Q i :=
      (exactIdentityAtom_is_optional_none T i).symm.trans (exactIdentityAtom_relation T i)
    calc
      R.rel = GroupActions.pullback (π i) (π i) (Quotient.image (π i) (π i) R.rel) :=
        (R.image_pullback_nested (π i) (π i) hn hn).symm
      _ = GroupActions.kernel (π i) := by rw [hatom,hc,hi]; rfl
      _ = B.rel := hK

end CCO.RigidGroupoid.Geometry
