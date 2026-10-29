import CCO.HKNReservoir.ProtectedTree

/-! C15--C17: one global normalization of a local tree map, followed by
an actual source realization. The complete protected base is fixed pointwise;
no injectivity is asserted between unrelated unrecorded pieces of the input. -/
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

/-- No protected base is needed to clear the ONE global language component
of an actual injective tree realization. -/
theorem literal_tree_realization {U V : Type (max v w)} [Finite U]
    (A : Structure L U) (hA : A.IsIrreducible)
    (a : Structure.Embedding act A N) {D : Structure L V}
    (T : TreePresentation act A D) :
    ∃ f : Structure.Homomorphism act D N, f.lang = 1 ∧
      Function.Injective f.toFun ∧
      Structure.Homomorphism.IsHomomorphismEmbedding act f := by
  obtain ⟨f,hf,he⟩ := actual_tree_realization S H R B hB Δ A hA a T.tree
  let inv := T.view.inverseSurjective act T.view_surjective
  let q := f.comp inv.toHomomorphism
  have hq : Function.Injective q.toFun := hf.comp inv.injective
  have hqe : Structure.Homomorphism.IsHomomorphismEmbedding act q :=
    Structure.Homomorphism.comp_isHomomorphismEmbedding act f inv.toHomomorphism he
      (Structure.Homomorphism.Embedding.toHomomorphism_isHomomorphismEmbedding act inv)
  obtain ⟨σ,hσ⟩ := ambientLift S H R B hB Δ q.lang⁻¹
  refine ⟨(σ.toEmbedding act).toHomomorphism.comp q,?_,
    (σ.toEmbedding act).injective.comp hq,
    Structure.Homomorphism.postcompose_automorphism_isHomomorphismEmbedding act q hqe σ⟩
  change σ.lang * q.lang = 1
  rw [hσ,inv_mul_cancel]

/-- A local homomorphism-embedding through a full-source tree yields a
literal named-source map fixing EVERY point of a prescribed complete base.
Normalization relabels the ENTIRE target and its whole tree presentation. -/
theorem protected_local_tree_readout {U J V W : Type (max v w)} [Finite U] [Finite J]
    (A : Structure L U) (hA : A.IsIrreducible)
    (a : Structure.Embedding act A N) {E : Structure L V} {D : Structure L W}
    (T : TreePresentation act A D) (h : Structure.Homomorphism act E D)
    (hh : Structure.Homomorphism.IsHomomorphismEmbedding act h)
    (P : Structure L J) (hP : P.IsIrreducible)
    (base : Structure.Embedding act P E) (old : Structure.Embedding act P N)
    (hl : old.lang = base.lang) :
    ∃ q : Structure.Homomorphism act E N, q.lang = 1 ∧
      Structure.Homomorphism.IsHomomorphismEmbedding act q ∧
      ∀ j, q (base j) = old j := by
  let h' := Homomorphism.normalize h
  have hh' : Structure.Homomorphism.IsHomomorphismEmbedding act h' :=
    Homomorphism.normalize_homomorphismEmbedding h hh
  let b := Structure.Homomorphism.compEmbedding_of_irreducible act h' hh' base hP
  have hbl : old.lang = b.lang := by
    change old.lang = h'.lang * base.lang
    rw [Homomorphism.normalize_lang,one_mul,hl]
  obtain ⟨f,hfl,hfi,hfe,hfix⟩ := protected_tree_realization S H R B hB Δ A hA a
    (T.relabelTarget h.lang⁻¹) P hP b old hbl
  refine ⟨f.comp h',?_,
    Structure.Homomorphism.comp_isHomomorphismEmbedding act f h' hfe hh',?_⟩
  · change f.lang * h'.lang = 1
    rw [hfl,Homomorphism.normalize_lang,mul_one]
  · intro j
    exact hfix j

/-- The unprotected local-tree implication has no nonempty-base premise.
Only the irreducible restrictions, rather than global input injectivity,
are retained when composing the local map with the injective realization. -/
theorem local_tree_readout {U V W : Type (max v w)} [Finite U]
    (A : Structure L U) (hA : A.IsIrreducible)
    (a : Structure.Embedding act A N) {E : Structure L V} {D : Structure L W}
    (T : TreePresentation act A D) (h : Structure.Homomorphism act E D)
    (hh : Structure.Homomorphism.IsHomomorphismEmbedding act h) :
    ∃ q : Structure.Homomorphism act E N, q.lang = 1 ∧
      Structure.Homomorphism.IsHomomorphismEmbedding act q := by
  let h' := Homomorphism.normalize h
  have hh' : Structure.Homomorphism.IsHomomorphismEmbedding act h' :=
    Homomorphism.normalize_homomorphismEmbedding h hh
  obtain ⟨f,hfl,_,hfe⟩ := literal_tree_realization S H R B hB Δ A hA a
    (T.relabelTarget h.lang⁻¹)
  refine ⟨f.comp h',?_,
    Structure.Homomorphism.comp_isHomomorphismEmbedding act f h' hfe hh'⟩
  change f.lang * h'.lang = 1
  rw [hfl,Homomorphism.normalize_lang,mul_one]

end
end CCO.HKNReservoir
