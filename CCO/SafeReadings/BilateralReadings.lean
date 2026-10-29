import CCO.SafeReadings.MovingReadings

universe u v w z t r
namespace CCO.SafeReadings
open Selectors
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {Γ : Type z} [Group Γ] {N : Type t} {A : PureTagAction S Γ N}
variable {K : Type r} [CommGroup K] (E : EndpointGauge S A K)

/-- PC means support at each of the three distinct formal vertices;
named sorts and menu values may repeat. -/
theorem pc_iff_all_support {i j k : ι} (D : S.Menu i j) (F : S.Menu j k) (P : S.Menu i k) :
    S.PC D F P ↔
      (∀ c ∈ P, ∃ a ∈ D, ∃ b ∈ F, S.Triangle a b c) ∧
      (∀ a ∈ D, ∃ b ∈ F, ∃ c ∈ P, S.Triangle a b c) ∧
      (∀ b ∈ F, ∃ a ∈ D, ∃ c ∈ P, S.Triangle a b c) := by
  constructor
  · intro hp
    refine ⟨hp.1,?_,?_⟩
    · intro a ha
      obtain ⟨c,hc,b,hb,ht⟩ := hp.2.1 ha
      refine ⟨S.conv b,hb,c,hc,?_⟩
      apply S.triangle_rotate_back
      simpa only [S.conv_invol] using ht
    · intro b hb
      obtain ⟨a,ha,c,hc,ht⟩ := hp.2.2 hb
      refine ⟨S.conv a,ha,c,hc,?_⟩
      simpa only [S.conv_invol] using S.triangle_rotate (S.triangle_cycle ht)
  · rintro ⟨hP,hD,hF⟩
    refine ⟨hP,?_,?_⟩
    · intro a ha
      obtain ⟨b,hb,c,hc,ht⟩ := hD a ha
      exact ⟨c,hc,S.conv b,S.mem_opposite hb,S.triangle_rotate ht⟩
    · intro b hb
      obtain ⟨a,ha,c,hc,ht⟩ := hF b hb
      exact ⟨S.conv a,S.mem_opposite ha,c,hc,S.triangle_rotate_back (S.triangle_cycle ht)⟩

/-- Actual equivalences of all three palettes transport all PC
coordinates, provided actual triangles are transported. -/
theorem pc_equiv {i j k i' j' k' : ι}
    (e : S.Atom i j ≃ S.Atom i' j') (f : S.Atom j k ≃ S.Atom j' k')
    (p : S.Atom i k ≃ S.Atom i' k')
    (ht : ∀ a b c, S.Triangle a b c ↔ S.Triangle (e a) (f b) (p c))
    (D : S.Menu i j) (F : S.Menu j k) (P : S.Menu i k)
    (hp : S.PC D F P) : S.PC (e '' D) (f '' F) (p '' P) := by
  rw [pc_iff_all_support] at hp ⊢
  constructor
  · rintro _ ⟨c,hc,rfl⟩
    obtain ⟨a,ha,b,hb,ht₀⟩ := hp.1 c hc
    exact ⟨e a,⟨a,ha,rfl⟩,f b,⟨b,hb,rfl⟩,(ht a b c).mp ht₀⟩
  constructor
  · rintro _ ⟨a,ha,rfl⟩
    obtain ⟨b,hb,c,hc,ht₀⟩ := hp.2.1 a ha
    exact ⟨f b,⟨b,hb,rfl⟩,p c,⟨c,hc,rfl⟩,(ht a b c).mp ht₀⟩
  · rintro _ ⟨b,hb,rfl⟩
    obtain ⟨a,ha,c,hc,ht₀⟩ := hp.2.2 b hb
    exact ⟨e a,⟨a,ha,rfl⟩,p c,⟨c,hc,rfl⟩,(ht a b c).mp ht₀⟩

theorem outer_PC (g k : K) {i j l : ι} (D : S.Menu i j) (F : S.Menu j l) (P : S.Menu i l)
    (hp : S.PC D F P) :
    S.PC (E.leftMenu g D) (E.rightMenu k F) (E.leftMenu g (E.rightMenu k P)) := by
  have h := pc_equiv (E.left g) (E.right k) ((E.right k).trans (E.left g))
    (fun a b c => (E.triangle_right k a b c).trans (E.triangle_left g a (E.right k b) (E.right k c))) D F P hp
  change S.PC (E.leftMenu g D) (E.rightMenu k F) (_ '' P) at h
  simpa only [EndpointGauge.leftMenu,EndpointGauge.rightMenu,Set.image_image,Equiv.coe_trans,Function.comp_def] using h

/-- The pure diagonal comparison identifies a right-switch choice
with the right switch of the moved-first reading. -/
theorem right_reading (h : HereditarySelector S) (hCov : h.Covariant S A)
    (g : K) {i j : ι} (D : S.Menu i j) (hD : StrongExact.Exact S D) :
    E.right g (reading E h g D hD) = h.choose (E.rightMenu g D) (E.right_exact g hD) := by
  apply A.label_injective
  rw [E.right_label,reading_label,E.switch_twice]
  exact left_right_choice_label E h hCov g D hD

/-- Two independent readings of adjacent menus are supported inside
every original PC third menu. -/
theorem reading_pair_supported (h : HereditarySelector S) (hCov : h.Covariant S A)
    (g k : K) {i j l : ι} (D : S.Menu i j) (F : S.Menu j l) (P : S.Menu i l)
    (hD : StrongExact.Exact S D) (hF : StrongExact.Exact S F) (hP : StrongExact.Exact S P)
    (hp : S.PC D F P) :
    ∃ c ∈ P, S.Triangle (reading E h g D hD) (reading E h k F hF) c := by
  have ht := h.triangle S (E.leftMenu g D) (E.rightMenu k F) (E.leftMenu g (E.rightMenu k P))
    (E.left_exact g hD) (E.right_exact k hF) (E.left_exact g (E.right_exact k hP)) (outer_PC E g k D F P hp)
  obtain ⟨c₁,⟨c,hc,hc₁⟩,hc₂⟩ := h.member (E.leftMenu g (E.rightMenu k P)) (E.left_exact g (E.right_exact k hP))
  rw [←left_reading E h g D hD,←right_reading E h hCov k F hF,←hc₂,←hc₁] at ht
  exact ⟨c,hc,(E.triangle_right k _ _ _).mpr ((E.triangle_left g _ _ _).mpr ht)⟩

end CCO.SafeReadings
