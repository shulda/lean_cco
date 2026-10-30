import CCO.ResetOrder.Hierarchy.Maps

/-! A sigma of transition orbits is a reindexing of the finite task set.
Coordinate priorities need not be equivariant under transitions. -/
universe u v w
namespace CCO.ResetOrder.Hierarchy
structure Charting {R : Type u} {J : R → Type u} {H : Schedule (Sigma J)}
    {X : Sigma J → Type v} (S : System H X) (representative : ∀ r, J r) where
  paths : ∀ r, TransitionPaths.{u,v,w} (J r) (fun j => X ⟨r,j⟩)
  chosen : ∀ r j, (paths r).Path (representative r) j
  parent_transport : ∀ r {j k} (p : (paths r).Path j k) x y,
    S.parent ⟨r,k⟩ ((paths r).map p x) ((paths r).map p y) ↔ S.parent ⟨r,j⟩ x y
  rank_orbit : ∀ r j, H.rank ⟨r,j⟩ = H.rank ⟨r,representative r⟩

namespace Charting
variable {R : Type u} {J : R → Type u} {H : Schedule (Sigma J)}
variable {X : Sigma J → Type v} {S : System H X} {rep : ∀ r, J r} (C : Charting.{u,v,w} S rep)
abbrev representative (_C : Charting.{u,v,w} S rep) := rep

def back (r : R) (j : J r) : X ⟨r,j⟩ ≃ X ⟨r,C.representative r⟩ :=
  ((C.paths r).map (C.chosen r j)).symm

theorem back_representative (r : R) (x : X ⟨r,C.representative r⟩) :
    C.back r (C.representative r) x = x := by
  apply ((C.paths r).map (C.chosen r (C.representative r))).injective
  unfold back
  rw [Equiv.apply_symm_apply, (C.paths r).holonomy]

theorem back_commute (r : R) {j k : J r} (p : (C.paths r).Path j k) (x : X ⟨r,j⟩) :
    C.back r k ((C.paths r).map p x) = C.back r j x := by
  apply ((C.paths r).map (C.chosen r k)).injective
  unfold back
  rw [Equiv.apply_symm_apply]
  rw [(C.paths r).path_independent (C.chosen r k) ((C.paths r).compose (C.chosen r j) p)]
  rw [(C.paths r).map_compose, Equiv.apply_symm_apply]

theorem parent_back (r : R) (j : J r) (x y : X ⟨r,j⟩) :
    S.parent ⟨r,C.representative r⟩ (C.back r j x) (C.back r j y) ↔ S.parent ⟨r,j⟩ x y := by
  have h := C.parent_transport r (C.chosen r j) (C.back r j x) (C.back r j y)
  simpa only [back, Equiv.apply_symm_apply] using h.symm

def localTasks (o : S.Orders) : S.Tasks := fun ⟨r,j⟩ => {
  lt := fun x y => S.parent ⟨r,j⟩ x y ∧
    (o ⟨r,C.representative r⟩).lt (C.back r j x) (C.back r j y)
  same := And.left
  irrefl := fun x h => (o ⟨r,C.representative r⟩).irrefl _ h.2
  trans := fun h h' => ⟨S.parent_trans _ h.1 h'.1,
    (o ⟨r,C.representative r⟩).trans h.2 h'.2⟩
  total := fun hp hxy => ((o ⟨r,C.representative r⟩).total
    (fun h => hxy ((C.back r j).injective h))).imp
      (fun h => ⟨hp,h⟩) (fun h => ⟨S.parent_symm _ hp,h⟩)
}

theorem localTasks_synchronized (o : S.Orders) (r : R) {j k : J r}
    (p : (C.paths r).Path j k) (x y : X ⟨r,j⟩) :
    (C.localTasks o ⟨r,k⟩).lt ((C.paths r).map p x) ((C.paths r).map p y) ↔
      (C.localTasks o ⟨r,j⟩).lt x y := by
  change (_ ∧ _) ↔ (_ ∧ _)
  rw [C.parent_transport, C.back_commute, C.back_commute]

theorem extract_tasks (o : S.Orders) :
    C.localTasks (S.normalizeTasks (C.localTasks o)) = C.localTasks o := by
  funext i
  obtain ⟨r,j⟩ := i
  apply FibreOrder.ext
  intro x y
  change (S.parent ⟨r,j⟩ x y ∧
      (S.normalizeTasks (C.localTasks o) ⟨r,C.representative r⟩).lt
        (C.back r j x) (C.back r j y)) ↔ _
  by_cases hp : S.parent ⟨r,j⟩ x y
  · have hb := (C.parent_back r j x y).2 hp
    rw [S.normalized_fibre _ _ hb]
    change (_ ∧ (_ ∧ (o _).lt (C.back r _ (C.back r j x))
      (C.back r _ (C.back r j y)))) ↔ _
    rw [C.back_representative, C.back_representative]
    exact ⟨fun h => ⟨h.1,h.2.2⟩, fun h => ⟨h.1,hb,h.2⟩⟩
  · change (_ ∧ _) ↔ (_ ∧ _)
    simp only [hp, false_and]

noncomputable def normalize (o : S.Orders) : S.Orders := S.normalizeTasks (C.localTasks o)
theorem normalize_idempotent (o : S.Orders) : C.normalize (C.normalize o) = C.normalize o := by
  unfold normalize
  rw [C.extract_tasks]

def Synchronized (o : S.Orders) : Prop :=
  ∀ r {j k} (p : (C.paths r).Path j k) x y, S.parent ⟨r,j⟩ x y →
    ((o ⟨r,k⟩).lt ((C.paths r).map p x) ((C.paths r).map p y) ↔ (o ⟨r,j⟩).lt x y)

theorem normalize_synchronized (o : S.Orders) : C.Synchronized (C.normalize o) := by
  intro r j k p x y hp
  have hp' := (C.parent_transport r p x y).2 hp
  exact (S.normalized_fibre _ _ hp').trans
    ((C.localTasks_synchronized o r p x y).trans (S.normalized_fibre _ _ hp).symm)

theorem synchronized_extract (o : S.Orders) (ho : C.Synchronized o) : C.localTasks o = S.extract o := by
  funext i
  obtain ⟨r,j⟩ := i
  apply FibreOrder.ext
  intro x y
  change (_ ∧ _) ↔ (_ ∧ _)
  apply and_congr_right
  intro hp
  have h := ho r (C.chosen r j) (C.back r j x) (C.back r j y)
    ((C.parent_back r j x y).2 hp)
  simpa only [back, Equiv.apply_symm_apply] using h.symm

theorem normalize_parentLex (o : S.Orders) : S.ParentLex (C.normalize o) := by
  have h := S.normalize_parentLex (C.normalize o)
  have hx : S.normalize (C.normalize o) = C.normalize o := by
    unfold System.normalize normalize
    rw [S.extract_normalize]
  exact hx ▸ h

theorem fixed_iff_image (o : S.Orders) : C.normalize o = o ↔ S.ParentLex o ∧ C.Synchronized o := by
  constructor
  · intro h
    rw [← h]
    exact ⟨C.normalize_parentLex o, C.normalize_synchronized o⟩
  · rintro ⟨hp, hs⟩
    unfold normalize
    rw [C.synchronized_extract o hs]
    exact S.parentLex_fixed o hp
end Charting
end CCO.ResetOrder.Hierarchy
