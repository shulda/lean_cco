import Mathlib.LinearAlgebra.Goursat

/-!
# Canonical actual subdirect linear pair checks

The two kernels are proved to be exactly the motions paired with zero. The
pinned Goursat theorem is applied to THIS submodule with its actual surjective
projections. Its quotient graph is pulled back without choosing point lifts.
Both endpoint checks are onto one common quotient, including the zero quotient.
-/

universe u v w
namespace CCO.FiniteKernel.Named

variable {K : Type u} [Field K] {V : Type v} {W : Type w}
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

abbrev leftKernel (P : Submodule K (V × W)) := P.goursatFst
abbrev rightKernel (P : Submodule K (V × W)) := P.goursatSnd

theorem mem_leftKernel (P : Submodule K (V × W)) (x : V) :
    x ∈ leftKernel P ↔ (x,0) ∈ P := by
  constructor
  · rintro ⟨z,hz,hzx⟩
    have he : z.val = (x,0) := Prod.ext hzx hz
    exact he ▸ z.property
  · intro hx
    exact ⟨⟨(x,0),hx⟩,rfl,rfl⟩

theorem mem_rightKernel (P : Submodule K (V × W)) (y : W) :
    y ∈ rightKernel P ↔ (0,y) ∈ P := by
  constructor
  · rintro ⟨z,hz,hzy⟩
    have he : z.val = (0,y) := Prod.ext hz hzy
    exact he ▸ z.property
  · intro hy
    exact ⟨⟨(0,y),hy⟩,rfl,rfl⟩

variable (P : Submodule K (V × W))
variable (hleft : Function.Surjective (Prod.fst ∘ P.subtype))
variable (hright : Function.Surjective (Prod.snd ∘ P.subtype))

noncomputable def quotientEquiv : (V ⧸ leftKernel P) ≃ₗ[K] (W ⧸ rightKernel P) :=
  Classical.choose (Submodule.goursat_surjective hleft hright)

theorem quotientEquiv_graph :
    P.map ((leftKernel P).mkQ.prodMap (rightKernel P).mkQ) =
      (quotientEquiv P hleft hright).toLinearMap.graph := by
  have hh := Classical.choose_spec (Submodule.goursat_surjective hleft hright)
  simpa only [quotientEquiv,LinearMap.range_comp,Submodule.range_subtype] using hh

theorem mem_pair_iff_quotient (x : V) (y : W) :
    (x,y) ∈ P ↔ quotientEquiv P hleft hright ((leftKernel P).mkQ x) = (rightKernel P).mkQ y := by
  let q := (leftKernel P).mkQ.prodMap (rightKernel P).mkQ
  have hker : q.ker ≤ P := by
    simpa only [q,LinearMap.ker_prodMap,Submodule.ker_mkQ] using
      P.goursatFst_prod_goursatSnd_le
  have hp : ((quotientEquiv P hleft hright).toLinearMap.graph).comap q = P := by
    rw [← quotientEquiv_graph P hleft hright]
    exact Submodule.comap_map_eq_self hker
  have hm : (x,y) ∈ P ↔ q (x,y) ∈ (quotientEquiv P hleft hright).toLinearMap.graph := by
    exact (congrArg (fun T : Submodule K (V × W) => (x,y) ∈ T) hp).to_iff.symm
  exact hm.trans ((LinearMap.mem_graph_iff _ _).trans eq_comm)

/-- One common quotient, chosen on the left, for both actual pair checks. -/
abbrev CommonSpace := V ⧸ leftKernel P

def leftCheck : V →ₗ[K] CommonSpace P := (leftKernel P).mkQ

noncomputable def rightCheck : W →ₗ[K] CommonSpace P :=
  (quotientEquiv P hleft hright).symm.toLinearMap.comp (rightKernel P).mkQ

theorem leftCheck_surjective : Function.Surjective (leftCheck P) :=
  (leftKernel P).mkQ_surjective

theorem rightCheck_surjective : Function.Surjective (rightCheck P hleft hright) :=
  (quotientEquiv P hleft hright).symm.surjective.comp (rightKernel P).mkQ_surjective

theorem mem_pair_iff_checks (x : V) (y : W) :
    (x,y) ∈ P ↔ leftCheck P x = rightCheck P hleft hright y := by
  rw [mem_pair_iff_quotient P hleft hright]
  exact (quotientEquiv P hleft hright).eq_symm_apply.symm

/-- The graph condition determines the quotient isomorphism uniquely. -/
theorem quotientEquiv_unique
    (e : (V ⧸ leftKernel P) ≃ₗ[K] (W ⧸ rightKernel P))
    (he : ∀ x y, (x,y) ∈ P → e ((leftKernel P).mkQ x) = (rightKernel P).mkQ y) :
    e = quotientEquiv P hleft hright := by
  apply LinearEquiv.ext
  intro q
  obtain ⟨x,rfl⟩ := (leftKernel P).mkQ_surjective q
  obtain ⟨z,hz⟩ := hleft x
  have hx : z.val.1 = x := hz
  have hp : (x,z.val.2) ∈ P := by simpa only [← hx] using z.property
  exact (he _ _ hp).trans ((mem_pair_iff_quotient P hleft hright x z.val.2).mp hp).symm

end CCO.FiniteKernel.Named
