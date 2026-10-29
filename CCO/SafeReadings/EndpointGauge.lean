import CCO.Selectors.SourceSelectors

/-! Abstract endpoint transport of ACTUAL typed atom palettes. Literal
fine names, endpoint tags and independent vertex switches remain separate.
No safe palette, source countability or original exactness field is assumed. -/
universe u v w z t r
namespace CCO.SafeReadings
open Selectors
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {Γ : Type z} [Group Γ] {N : Type t} (A : PureTagAction S Γ N)

structure EndpointGauge (K : Type r) [CommGroup K] where
  square : ∀ g : K, g * g = 1
  owner : K →* Equiv.Perm ι
  switch : K →* Equiv.Perm N
  left : ∀ (g : K) {i j : ι}, S.Atom i j ≃ S.Atom (owner g i) j
  right : ∀ (g : K) {i j : ι}, S.Atom i j ≃ S.Atom i (owner g j)
  left_label : ∀ (g : K) {i j : ι} (a : S.Atom i j), A.label (left g a) = switch g (A.label a)
  right_label : ∀ (g : K) {i j : ι} (a : S.Atom i j), A.label (right g a) = switch g (A.label a)
  triangle_left : ∀ (g : K) {i j k : ι} (a : S.Atom i j) (b : S.Atom j k) (c : S.Atom i k),
    S.Triangle a b c ↔ S.Triangle (left g a) b (left g c)
  triangle_right : ∀ (g : K) {i j k : ι} (a : S.Atom i j) (b : S.Atom j k) (c : S.Atom i k),
    S.Triangle a b c ↔ S.Triangle a (right g b) (right g c)
  diagonal : K → Γ
  diagonal_owner : ∀ g, A.tag (diagonal g) = owner g
  commute : ∀ (γ : Γ) (g : K) i, A.tag γ (owner g i) = owner g (A.tag γ i)

namespace EndpointGauge
variable {S A} {K : Type r} [CommGroup K] (E : EndpointGauge S A K)

@[simp] theorem owner_twice (g : K) (i : ι) : E.owner g (E.owner g i) = i := by
  have h := congrArg (fun p : Equiv.Perm ι => p i) (E.owner.map_mul g g)
  rw [E.square,map_one] at h
  exact h.symm

@[simp] theorem switch_twice (g : K) (n : N) : E.switch g (E.switch g n) = n := by
  have h := congrArg (fun p : Equiv.Perm N => p n) (E.switch.map_mul g g)
  rw [E.square,map_one] at h
  exact h.symm

def leftMenu (g : K) {i j : ι} (D : S.Menu i j) : S.Menu (E.owner g i) j := E.left g '' D
def rightMenu (g : K) {i j : ι} (D : S.Menu i j) : S.Menu i (E.owner g j) := E.right g '' D

@[simp] theorem mem_leftMenu (g : K) {i j : ι} (D : S.Menu i j) (a : S.Atom i j) :
    E.left g a ∈ E.leftMenu g D ↔ a ∈ D := by
  exact E.left g |>.injective.mem_set_image

@[simp] theorem mem_rightMenu (g : K) {i j : ι} (D : S.Menu i j) (a : S.Atom i j) :
    E.right g a ∈ E.rightMenu g D ↔ a ∈ D := by
  exact E.right g |>.injective.mem_set_image

@[simp] theorem leftMenu_univ (g : K) (i j : ι) :
    E.leftMenu g (Set.univ : S.Menu i j) = Set.univ := Set.image_univ.trans (E.left g).surjective.range_eq
@[simp] theorem rightMenu_univ (g : K) (i j : ι) :
    E.rightMenu g (Set.univ : S.Menu i j) = Set.univ := Set.image_univ.trans (E.right g).surjective.range_eq

@[simp] theorem leftMenu_singleton (g : K) {i j : ι} (a : S.Atom i j) :
    E.leftMenu g {a} = {E.left g a} := Set.image_singleton
@[simp] theorem rightMenu_singleton (g : K) {i j : ι} (a : S.Atom i j) :
    E.rightMenu g {a} = {E.right g a} := Set.image_singleton

theorem leftMenu_inter (g : K) {i j : ι} (D F : S.Menu i j) :
    E.leftMenu g (D ∩ F) = E.leftMenu g D ∩ E.leftMenu g F :=
  Set.image_inter (E.left g).injective

theorem rightMenu_inter (g : K) {i j : ι} (D F : S.Menu i j) :
    E.rightMenu g (D ∩ F) = E.rightMenu g D ∩ E.rightMenu g F :=
  Set.image_inter (E.right g).injective

/-- Unilateral switching transports arbitrary-subset strong products. -/
theorem leftMenu_product (g : K) {i j k : ι} (D : S.Menu i j) (F : S.Menu j k) :
    E.leftMenu g (S.product D F) = S.product (E.leftMenu g D) F := by
  apply Set.Subset.antisymm
  · rintro _ ⟨c,⟨a,ha,b,hb,ht⟩,rfl⟩
    exact ⟨E.left g a,⟨a,ha,rfl⟩,b,hb,(E.triangle_left g a b c).mp ht⟩
  · rintro c ⟨_,⟨a,ha,rfl⟩,b,hb,ht⟩
    let c₀ := (E.left g).symm c
    have hc : E.left g c₀ = c := (E.left g).apply_symm_apply c
    exact ⟨c₀,⟨a,ha,b,hb,(E.triangle_left g a b c₀).mpr (hc ▸ ht)⟩,hc⟩

theorem rightMenu_product (g : K) {i j k : ι} (D : S.Menu i j) (F : S.Menu j k) :
    E.rightMenu g (S.product D F) = S.product D (E.rightMenu g F) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨c,⟨a,ha,b,hb,ht⟩,rfl⟩
    exact ⟨a,ha,E.right g b,⟨b,hb,rfl⟩,(E.triangle_right g a b c).mp ht⟩
  · rintro c ⟨a,ha,_,⟨b,hb,rfl⟩,ht⟩
    let c₀ := (E.right g).symm c
    have hc : E.right g c₀ = c := (E.right g).apply_symm_apply c
    exact ⟨c₀,⟨a,ha,b,hb,(E.triangle_right g a b c₀).mpr (hc ▸ ht)⟩,hc⟩

/-- Both unilateral moves use the same literal colour involution. -/
theorem names_leftMenu (g : K) {i j : ι} (D : S.Menu i j) :
    names S A.label ⟨E.owner g i,j,E.leftMenu g D⟩ = E.switch g '' names S A.label ⟨i,j,D⟩ := by
  ext n
  constructor
  · rintro ⟨_,⟨a,ha,rfl⟩,hn⟩
    exact ⟨A.label a,⟨a,ha,rfl⟩,(E.left_label g a).symm.trans hn⟩
  · rintro ⟨_,⟨a,ha,rfl⟩,hn⟩
    exact ⟨E.left g a,⟨a,ha,rfl⟩,(E.left_label g a).trans hn⟩

theorem names_rightMenu (g : K) {i j : ι} (D : S.Menu i j) :
    names S A.label ⟨i,E.owner g j,E.rightMenu g D⟩ = E.switch g '' names S A.label ⟨i,j,D⟩ := by
  ext n
  constructor
  · rintro ⟨_,⟨a,ha,rfl⟩,hn⟩
    exact ⟨A.label a,⟨a,ha,rfl⟩,(E.right_label g a).symm.trans hn⟩
  · rintro ⟨_,⟨a,ha,rfl⟩,hn⟩
    exact ⟨E.right g a,⟨a,ha,rfl⟩,(E.right_label g a).trans hn⟩

end EndpointGauge
end CCO.SafeReadings
