import CCO.HKNReservoir.RealizedClass
import CCO.HKNReservoir.LanguageNormalization

/-! C08: an actual closed-SAP tree can be realized with its entire prescribed
complete irreducible interface fixed. One ambient owner lift clears the ONE
global language component; an actual named automorphism then aligns the
whole interface, without choosing independent components on tree nodes. -/
universe v w t
namespace CCO.HKNReservoir
noncomputable section
open AllThoseEPPA ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)
variable (Δ : Subgroup (SourceGamma S H R B))
set_option quotPrecheck false
local notation "L" => Signature ↥B (ResidualData.PacketGroup S H) (S.Atom () ())
local notation "act" => sourceAction S H R B Δ
local notation "N" => sourceStructure S H R B hB

/-- A globally injective, literal-language tree realization fixing EVERY
point of a prescribed complete closed irreducible base. The source instance
of closed SAP and named homogeneity is discharged by the residual data. -/
theorem protected_tree_realization {U J V : Type (max v w)} [Finite U] [Finite J]
    (A : Structure L U) (hA : A.IsIrreducible)
    (a : Structure.Embedding act A N) {D : Structure L V}
    (T : TreePresentation act A D) (P : Structure L J) (hP : P.IsIrreducible)
    (base : Structure.Embedding act P D) (old : Structure.Embedding act P N)
    (hl : old.lang = base.lang) :
    ∃ f : Structure.Homomorphism act D N, f.lang = 1 ∧
      Function.Injective f.toFun ∧
      Structure.Homomorphism.IsHomomorphismEmbedding act f ∧
      ∀ j, f (base j) = old j := by
  classical
  obtain ⟨f,hf,he⟩ := actual_tree_realization S H R B hB Δ A hA a T.tree
  let inv := T.view.inverseSurjective act T.view_surjective
  let q := f.comp inv.toHomomorphism
  have hq : Function.Injective q.toFun := hf.comp inv.injective
  have hqe : Structure.Homomorphism.IsHomomorphismEmbedding act q :=
    Structure.Homomorphism.comp_isHomomorphismEmbedding act f inv.toHomomorphism he
      (Structure.Homomorphism.Embedding.toHomomorphism_isHomomorphismEmbedding act inv)
  obtain ⟨σ,hσ⟩ := ambientLift S H R B hB Δ q.lang⁻¹
  let g := (σ.toEmbedding act).toHomomorphism.comp q
  have hg : Function.Injective g.toFun := (σ.toEmbedding act).injective.comp hq
  have hge : Structure.Homomorphism.IsHomomorphismEmbedding act g :=
    Structure.Homomorphism.postcompose_automorphism_isHomomorphismEmbedding act q hqe σ
  have hgl : g.lang = 1 := by
    change σ.lang * q.lang = 1
    rw [hσ,inv_mul_cancel]
  let b := Structure.Homomorphism.compEmbedding_of_irreducible act g hge base hP
  have hbl : b.lang = old.lang := by
    change g.lang * base.lang = old.lang
    rw [hgl,one_mul,hl]
  let Q := namedRange S H R B old.toFun
  have hQ (j : J) : (old j).down ∈ Q :=
    (mem_namedRange S H R B old.toFun _).mpr ⟨j,rfl⟩
  let e := rangeCorrespondence S H R B hB Δ b old hbl Q hQ
  obtain ⟨k,hk⟩ := named_embedding_extends S H R B
    (namedRange S H R B b.toFun) Q e
  let r := ((namedAut S H R B hB Δ k).toEmbedding act).toHomomorphism.comp g
  refine ⟨r,?_,(namedAut S H R B hB Δ k).toEmbedding act |>.injective.comp hg,
    Structure.Homomorphism.postcompose_automorphism_isHomomorphismEmbedding act g hge
      (namedAut S H R B hB Δ k),?_⟩
  · change 1 * g.lang = 1
    exact (one_mul _).trans hgl
  · intro j
    apply ULift.ext
    let x : ↥(namedRange S H R B b.toFun) :=
      ⟨(b j).down,(mem_namedRange S H R B b.toFun _).mpr ⟨j,rfl⟩⟩
    have hx := hk x
    have heq := rangeCorrespondence_apply S H R B hB Δ b old hbl Q hQ j
    change k.val (b j).down = (e.toEmbedding x).val at hx
    exact hx.trans heq

end
end CCO.HKNReservoir
