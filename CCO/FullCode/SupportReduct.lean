import CCO.FullCode.ExpandedRestriction
import CCO.FullCode.LanguageExpansion

/-! The source's marked support/reduct hypothesis, stated for actual complete
root codes, and its consequences for ADDED-function closure. -/

universe u v w a
namespace CCO.FullCode
variable {L₀ L₁ : Language.{u}} {V : Type v} {W : Type w}

def rootCoordinates {L : Language.{u}} {C : Structure L V} {S : RootScheme L}
    (T : Set (Root C S)) : Set V :=
  {x | ∃ r ∈ T, ∃ j, r.coordinate j = x}

/-- A07: for every actual hereditary root code, expanded generation forgets
to the SAME old generated support over the SAME coordinate presentations.
This is not inferred from finite normal forms when functions are added. -/
def SupportReductCommutes (ρ : LanguageExpansion L₀ L₁)
    (S : RootScheme L₀) (C : Structure L₁ V) : Prop :=
  ∀ T : Set (Root C (S.lift ρ)),
    C.closure (rootCoordinates T) = (C.reduct ρ.toReduct).closure (rootCoordinates T)

namespace Object
variable {ρ : LanguageExpansion L₀ L₁} {S : RootScheme L₀}
  {C : Structure L₁ V} {A : Type a}

def toOld (O : Object C (S.lift ρ) A) : Object (C.reduct ρ.toReduct) S A where
  root a := (O.root a).toOld ρ
  injective := (Root.expansionEquiv ρ C S).injective.comp O.injective

@[simp] theorem toOld_coordinates (O : Object C (S.lift ρ) A) :
    (O.toOld).coordinates = O.coordinates := rfl

theorem support_reduct_eq_of_commutes (O : Object C (S.lift ρ) A)
    (commutes : SupportReductCommutes ρ S C) : O.support = O.toOld.support := by
  have hcoord : rootCoordinates (Set.range O.root) = O.coordinates := by
    ext x
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, j, hj⟩
      exact ⟨a, j, hj⟩
    · rintro ⟨a, j, hj⟩
      exact ⟨O.root a, ⟨a, rfl⟩, j, hj⟩
  have h := commutes (Set.range O.root)
  rw [hcoord] at h
  exact h

/-- Contract (i)'s actual expanded source support has an OLD-root-generated
reduct.  This closes the normalization premise for every visible source. -/
theorem reduct_support_rootGenerated (O : Object C (S.lift ρ) A)
    (commutes : SupportReductCommutes ρ S C) :
    RootGenerated (O.supportStructure.reduct ρ.toReduct) S := by
  apply Set.eq_univ_of_forall
  intro x
  let i := (C.inclusion O.support (C.isClosed_closure O.coordinates)).reduct ρ.toReduct
  have hcoord : O.coordinates ⊆
      i.point '' (Object.full (O.supportStructure.reduct ρ.toReduct) S).coordinates := by
    rintro _ ⟨a, j, rfl⟩
    exact ⟨⟨(O.root a).coordinate j, O.coordinate_mem_support a j⟩,
      ⟨(O.markedRoot a).toOld ρ, j, rfl⟩, rfl⟩
  have hx : x.val ∈ (C.reduct ρ.toReduct).closure O.coordinates := by
    change x.val ∈ O.toOld.support
    rw [← O.support_reduct_eq_of_commutes commutes]
    exact x.property
  have h := (C.reduct ρ.toReduct).closure_minimal
    ((C.reduct ρ.toReduct).isClosed_closure
      (i.point '' (Object.full (O.supportStructure.reduct ρ.toReduct) S).coordinates))
    (hcoord.trans ((C.reduct ρ.toReduct).subset_closure _)) hx
  rw [i.closure_image] at h
  obtain ⟨y, hy, hyx⟩ := h
  exact (Subtype.ext hyx) ▸ hy

end Object

def mappedOldRoots (ρ : LanguageExpansion L₀ L₁) (S : RootScheme L₀)
    (D : Structure L₀ V) (C : Structure L₁ W)
    (j : Structure.Embedding D (C.reduct ρ.toReduct)) :
    Object C (S.lift ρ) (Root D S) where
  root r := (r.map j).toExpanded ρ
  injective := (Root.expansionEquiv ρ C S).symm.injective.comp (Root.map_injective j)

theorem mappedOldRoots_coordinates (ρ : LanguageExpansion L₀ L₁) (S : RootScheme L₀)
    (D : Structure L₀ V) (C : Structure L₁ W)
    (j : Structure.Embedding D (C.reduct ρ.toReduct)) :
    (mappedOldRoots ρ S D C j).coordinates = j.point '' (Object.full D S).coordinates := by
  ext y
  constructor
  · rintro ⟨r, k, hk⟩
    exact ⟨r.coordinate k, ⟨r, k, rfl⟩, hk⟩
  · rintro ⟨_, ⟨r, k, rfl⟩, hy⟩
    exact ⟨r, k, hy⟩

/-- C51: the image of ANY old-root-generated host is actually closed under
all added functions in ANY competing expansion satisfying the source's
uniform actual support/reduct compatibility. -/
theorem expanded_image_closed (ρ : LanguageExpansion L₀ L₁) (S : RootScheme L₀)
    (D : Structure L₀ V) (C : Structure L₁ W)
    (j : Structure.Embedding D (C.reduct ρ.toReduct))
    (generated : RootGenerated D S) (commutes : SupportReductCommutes ρ S C) :
    C.IsClosed (Set.range j.point) := by
  have h := (mappedOldRoots ρ S D C j).support_reduct_eq_of_commutes commutes
  change C.closure (mappedOldRoots ρ S D C j).coordinates =
    (C.reduct ρ.toReduct).closure (mappedOldRoots ρ S D C j).toOld.coordinates at h
  rw [Object.toOld_coordinates, mappedOldRoots_coordinates] at h
  exact C.image_expanded_closed_of_support_reduct_commutes ρ.toReduct D j
    (Object.full D S).coordinates generated h

end CCO.FullCode
