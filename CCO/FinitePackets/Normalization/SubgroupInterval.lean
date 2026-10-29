import CCO.FinitePackets.Normalization.Translations
import CCO.FinitePackets.Geometry.MinimalCutBasic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Order.WithBot
import Mathlib.Order.Hom.Set

/-! Actual colour-invariant equivalences below the thin finite bottom are
exactly subgroups of its translation group.  The minimal infinite cut adds
one new greatest element, with no distributivity or imaginary-action claim. -/
universe v w t
namespace CCO.FinitePackets.Normalization
open CCO.RealHull.Geometry CCO.ParityHasse.Original
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable (F : ColourEq S ()) {G : Type t} [Group G] [MulAction G M]

def equivalenceTranslations (E : ColourEq S ()) : Subgroup (Translation S F G) where
  carrier := {e | ∀ x : M, E x (e.val x)}
  one_mem' := fun x => E.val.refl x
  mul_mem' := by
    intro e f he hf x
    exact E.val.trans (hf x) (he (f.val x))
  inv_mem' := by
    intro e he x
    have hh := he (e.val.symm x)
    change E (e.val.symm x) (e.val (e.val.symm x)) at hh
    rw [Equiv.apply_symm_apply] at hh
    exact E.val.symm hh

def subgroupRelation (K : Subgroup (Translation S F G)) (x y : M) : Prop :=
  ∃ e : Translation S F G, e ∈ K ∧ e.val x = y

def subgroupSetoid (K : Subgroup (Translation S F G)) : Setoid M where
  r := subgroupRelation S F K
  iseqv := ⟨fun x => ⟨1,K.one_mem,rfl⟩,
    by
      rintro x y ⟨e,he,hxy⟩
      refine ⟨e⁻¹,K.inv_mem he,?_⟩
      change e.val.symm y = x
      rw [← hxy,Equiv.symm_apply_apply],
    by
      rintro x y z ⟨e,he,hxy⟩ ⟨f,hf,hyz⟩
      exact ⟨f*e,K.mul_mem hf he,by change f.val (e.val x) = z; rw [hxy,hyz]⟩⟩

variable (H : HomogeneousSource S G)
include H

theorem subgroupRelation_transport (K : Subgroup (Translation S F G))
    {x y x' y' : M} (hcol : col S x y = col S x' y') :
    subgroupRelation S F K x y → subgroupRelation S F K x' y' := by
  rintro ⟨e,he,hxy⟩
  obtain ⟨g,hgx,hgy⟩ := S.pair_homogeneous_of_homogeneous H x x' y y' hcol
  refine ⟨e,he,?_⟩
  rw [← hgx,translation_equivariant S F G,hxy,hgy]

def subgroupEquivalence (K : Subgroup (Translation S F G)) : ColourEq S () :=
  ⟨subgroupSetoid S F K,fun _ _ _ _ hc =>
    ⟨subgroupRelation_transport S F H K hc,subgroupRelation_transport S F H K hc.symm⟩⟩

theorem subgroupEquivalence_le (K : Subgroup (Translation S F G)) :
    subgroupEquivalence S F H K ≤ F := by
  rintro x y ⟨e,he,rfl⟩
  exact translation_in_packet S F G e x

theorem equivalenceTranslations_at (E : ColourEq S ()) (e : Translation S F G) (x : M)
    (hE : E x (e.val x)) : e ∈ equivalenceTranslations S F E := by
  intro y
  exact (E.property x (e.val x) y (e.val y)
    (translation_colour_constant S F H e x y)).mp hE

variable (hthin : ThinBottom S F)
include hthin

theorem subgroupEquivalence_equivalenceTranslations (E : ColourEq S ()) (hEF : E ≤ F) :
    subgroupEquivalence S F H (equivalenceTranslations S F E) = E := by
  apply ColourEq.ext
  intro x y
  constructor
  · rintro ⟨e,he,rfl⟩
    exact he x
  · intro hxy
    obtain ⟨e,he,hunique⟩ := translation_regular S F H hthin x y (hEF hxy)
    exact ⟨e,equivalenceTranslations_at S F H E e x (he.symm ▸ hxy),he⟩

theorem equivalenceTranslations_subgroupEquivalence (K : Subgroup (Translation S F G)) :
    equivalenceTranslations S F (subgroupEquivalence S F H K) = K := by
  apply Subgroup.ext
  intro e
  constructor
  · intro he
    let x := Classical.choice (S.nonemptySort ())
    obtain ⟨f,hf,hfe⟩ := he x
    have hEq : f = e := by
      apply (packetTranslationEquiv S F H hthin x).injective
      exact Subtype.ext hfe
    exact hEq ▸ hf
  · intro he x
    exact ⟨e,he,rfl⟩

noncomputable def finiteBottomSubgroupIso :
    Set.Iic F ≃o Subgroup (Translation S F G) where
  toFun E := equivalenceTranslations S F E.val
  invFun K := ⟨subgroupEquivalence S F H K,subgroupEquivalence_le S F H K⟩
  left_inv E := Subtype.ext (subgroupEquivalence_equivalenceTranslations S F H hthin E.val E.property)
  right_inv := equivalenceTranslations_subgroupEquivalence S F H hthin
  map_rel_iff' := by
    intro E D
    constructor
    · intro hED x y hxy
      obtain ⟨e,he,hunique⟩ := translation_regular S F H hthin x y (E.property hxy)
      have heE := equivalenceTranslations_at S F H E.val e x (he.symm ▸ hxy)
      have heD := hED heE
      exact he ▸ heD x
    · intro hED e he x
      exact hED (he x)

theorem equivalenceTranslations_mono {E D : ColourEq S ()} (hED : E ≤ D) :
    equivalenceTranslations S F (G := G) E ≤ equivalenceTranslations S F D :=
  fun _ he x => hED (he x)

/-- The subgroup attached to any actual equivalence below F, followed by
its own full subgroup interval.  This includes H=Id. -/
noncomputable def lowerEquivalenceSubgroupIso (E : ColourEq S ()) (hEF : E ≤ F) :
    Set.Iic E ≃o Subgroup (equivalenceTranslations S F (G := G) E) := by
  letI := ColourEq.lattice S H (i := ())
  let e := finiteBottomSubgroupIso S F H hthin
  let a : Set.Iic E ≃o Set.Iic (⟨E,hEF⟩ : Set.Iic F) := {
    toFun := fun J => ⟨⟨J.val,J.property.trans hEF⟩,J.property⟩
    invFun := fun J => ⟨J.val.val,J.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_rel_iff' := Iff.rfl }
  exact a.trans ((e.Iic ⟨E,hEF⟩).trans (Subgroup.MapSubtype.orderIso _).symm)

end CCO.FinitePackets.Normalization
