import CCO.SafeReadings.GaugeWords
import CCO.SafeReadings.MenuCalculus

universe u v w z t r
namespace CCO.SafeReadings
open Selectors
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {Γ : Type z} [Group Γ] {N : Type t} {A : PureTagAction S Γ N}
variable {K : Type r} [CommGroup K] (E : EndpointGauge S A K)
variable (h : HereditarySelector S)

/-- The selector is evaluated at the moved FIRST endpoint. -/
noncomputable def reading (g : K) {i j : ι} (D : S.Menu i j) (hD : StrongExact.Exact S D) : S.Atom i j :=
  (E.left g).symm (h.choose (E.leftMenu g D) (E.left_exact g hD))

theorem reading_member (g : K) {i j : ι} (D : S.Menu i j) (hD : StrongExact.Exact S D) :
    reading E h g D hD ∈ D := by
  have hm := h.member (E.leftMenu g D) (E.left_exact g hD)
  obtain ⟨a,ha,he⟩ := hm
  simpa only [reading,←he,Equiv.symm_apply_apply] using ha

@[simp] theorem left_reading (g : K) {i j : ι} (D : S.Menu i j) (hD : StrongExact.Exact S D) :
    E.left g (reading E h g D hD) = h.choose (E.leftMenu g D) (E.left_exact g hD) :=
  (E.left g).apply_symm_apply _

theorem reading_label (g : K) {i j : ι} (D : S.Menu i j) (hD : StrongExact.Exact S D) :
    A.label (reading E h g D hD) = E.switch g (A.label (h.choose (E.leftMenu g D) (E.left_exact g hD))) := by
  rw [←left_reading E h g D hD,E.left_label,E.switch_twice]

theorem reading_heredity (g : K) {i j : ι} (D F : S.Menu i j)
    (hD : StrongExact.Exact S D) (hF : StrongExact.Exact S F) (hFD : F ⊆ D)
    (hs : reading E h g D hD ∈ F) : reading E h g F hF = reading E h g D hD := by
  apply (E.left g).injective
  rw [left_reading,left_reading]
  apply h.heredity
  · exact Set.image_mono hFD
  · rw [←left_reading E h g D hD]
    exact ⟨_,hs,rfl⟩

def chooseName (D : TaggedMenu S) (hD : IsExact S D) : N := A.label (h.choose D.2.2 hD)

theorem chooseName_congr {D F : TaggedMenu S} (hD : IsExact S D) (hF : IsExact S F)
    (he : D = F) : chooseName (A:=A) h D hD = chooseName (A:=A) h F hF := by
  subst F
  rfl

/-- The diagonal pure owner move turns a moved-first menu into the
moved-second menu with exactly the same old literal names. -/
theorem diagonal_left_eq_right (g : K) {i j : ι} (D : S.Menu i j) :
    A.act (E.diagonal g) ⟨E.owner g i,j,E.leftMenu g D⟩ = ⟨i,E.owner g j,E.rightMenu g D⟩ := by
  apply A.tagged_names_injective
  · constructor
    · rw [A.source,E.diagonal_owner,E.owner_twice]
    · rw [A.target,E.diagonal_owner]
  · rw [A.literal,E.names_leftMenu,E.names_rightMenu]

theorem left_right_choice_label (hCov : h.Covariant S A) (g : K) {i j : ι}
    (D : S.Menu i j) (hD : StrongExact.Exact S D) :
    A.label (h.choose (E.leftMenu g D) (E.left_exact g hD)) =
      A.label (h.choose (E.rightMenu g D) (E.right_exact g hD)) := by
  have hc := hCov (E.diagonal g) ⟨E.owner g i,j,E.leftMenu g D⟩ (E.left_exact g hD)
  have he := chooseName_congr (A:=A) h (D:=A.act (E.diagonal g) ⟨E.owner g i,j,E.leftMenu g D⟩) (F:=⟨i,E.owner g j,E.rightMenu g D⟩) ((A.exact (E.diagonal g) ⟨E.owner g i,j,E.leftMenu g D⟩).mpr (E.left_exact g hD))
    (E.right_exact g hD) (diagonal_left_eq_right E g D)
  exact hc.symm.trans he

theorem left_conv (hConv : LiteralConverse S A) (g : K) {i j : ι} (a : S.Atom i j) :
    E.left g (S.conv a) = S.conv (E.right g a) := by
  apply A.label_injective
  rw [E.left_label,hConv,hConv,E.right_label]

theorem left_opposite (hConv : LiteralConverse S A) (g : K) {i j : ι} (D : S.Menu i j) :
    E.leftMenu g (S.opposite D) = S.opposite (E.rightMenu g D) := by
  ext a
  constructor
  · rintro ⟨b,hb,rfl⟩
    change S.conv (E.left g b) ∈ E.rightMenu g D
    refine ⟨S.conv b,hb,?_⟩
    simpa only [S.conv_invol] using (congrArg S.conv (left_conv E hConv g (S.conv b))).symm
  · intro ha
    obtain ⟨b,hb,he⟩ := ha
    refine ⟨S.conv b,by change S.conv (S.conv b) ∈ D; simpa only [S.conv_invol] using hb,?_⟩
    rw [left_conv E hConv g b,he,S.conv_invol]


theorem reading_converse (hCov : h.Covariant S A) (hConv : LiteralConverse S A)
    (g : K) {i j : ι} (D : S.Menu i j) (hD : StrongExact.Exact S D)
    (hO : StrongExact.Exact S (S.opposite D)) :
    reading E h g (S.opposite D) hO = S.conv (reading E h g D hD) := by
  apply A.label_injective
  rw [reading_label,hConv,reading_label]
  apply congrArg (E.switch g)
  have he := left_opposite E hConv g D
  have hh : A.label (h.choose (E.leftMenu g (S.opposite D)) (E.left_exact g hO)) =
      A.label (h.choose (S.opposite (E.rightMenu g D)) (by rw [←he]; exact E.left_exact g hO)) :=
    chooseName_congr (A:=A) h (D:=⟨E.owner g j,i,E.leftMenu g (S.opposite D)⟩)
      (F:=⟨E.owner g j,i,S.opposite (E.rightMenu g D)⟩) _ _ (by rw [he])
  rw [hh,h.opposite,hConv]
  exact (left_right_choice_label E h hCov g D hD).symm

/-- A pure tag move commutes with a unilateral switch at the level of
actual tagged menus, even when its action on owners is nonfaithful. -/
theorem pure_left_eq (γ : Γ) (g : K) (D : TaggedMenu S) :
    A.act γ ⟨E.owner g D.1,D.2.1,E.leftMenu g D.2.2⟩ =
      ⟨E.owner g (A.act γ D).1,(A.act γ D).2.1,E.leftMenu g (A.act γ D).2.2⟩ := by
  apply A.tagged_names_injective
  · constructor
    · change (A.act γ ⟨E.owner g D.1,D.2.1,E.leftMenu g D.2.2⟩).1 = E.owner g (A.act γ D).1
      exact (A.source _ _).trans ((E.commute γ g D.1).trans (congrArg (E.owner g) (A.source γ D).symm))
    · change (A.act γ ⟨E.owner g D.1,D.2.1,E.leftMenu g D.2.2⟩).2.1 = (A.act γ D).2.1
      exact (A.target _ _).trans (A.target γ D).symm
  · rw [A.literal,E.names_leftMenu,E.names_leftMenu,A.literal]

theorem reading_covariant (hCov : h.Covariant S A) (γ : Γ) (g : K)
    (D : TaggedMenu S) (hD : IsExact S D) :
    A.label (reading E h g (A.act γ D).2.2 ((A.exact γ D).mpr hD)) =
      A.label (reading E h g D.2.2 hD) := by
  change StrongExact.Exact S D.2.2 at hD
  have hAct : StrongExact.Exact S (A.act γ D).2.2 := (A.exact γ D).mpr hD
  change A.label (reading E h g (A.act γ D).2.2 hAct) = A.label (reading E h g D.2.2 hD)
  simp only [reading_label]
  apply congrArg (E.switch g)
  have he := chooseName_congr (A:=A) h
    (D:=A.act γ ⟨E.owner g D.1,D.2.1,E.leftMenu g D.2.2⟩)
    (F:=⟨E.owner g (A.act γ D).1,(A.act γ D).2.1,E.leftMenu g (A.act γ D).2.2⟩)
    ((A.exact _ _).mpr (E.left_exact g hD)) (E.left_exact g ((A.exact γ D).mpr hD))
    (pure_left_eq E γ g D)
  exact he.symm.trans (hCov γ ⟨E.owner g D.1,D.2.1,E.leftMenu g D.2.2⟩ (E.left_exact g hD))

theorem left_left_eq (u v : K) {i j : ι} (D : S.Menu i j) :
    (⟨E.owner (u*v) (E.owner v i),j,E.leftMenu (u*v) (E.leftMenu v D)⟩ : TaggedMenu S) =
      ⟨E.owner u i,j,E.leftMenu u D⟩ := by
  apply A.tagged_names_injective
  · constructor
    · simp only [map_mul,Equiv.Perm.mul_apply,E.owner_twice]
    · rfl
  · rw [E.names_leftMenu,E.names_leftMenu,E.names_leftMenu,Set.image_image]
    have he : (fun n => E.switch (u*v) (E.switch v n)) = E.switch u := by
      funext n
      simp only [map_mul,Equiv.Perm.mul_apply,E.switch_twice]
    rw [he]

/-- Moving FIRST types is essential in the switch identity. -/
theorem reading_switch (u v : K) {i j : ι} (D : S.Menu i j) (hD : StrongExact.Exact S D) :
    reading E h (u*v) (E.leftMenu v D) (E.left_exact v hD) =
      E.left v (reading E h u D hD) := by
  apply A.label_injective
  rw [reading_label,E.left_label,reading_label]
  have he := chooseName_congr (A:=A) h
    (D:=⟨E.owner (u*v) (E.owner v i),j,E.leftMenu (u*v) (E.leftMenu v D)⟩)
    (F:=⟨E.owner u i,j,E.leftMenu u D⟩)
    (E.left_exact (u*v) (E.left_exact v hD)) (E.left_exact u hD) (left_left_eq E u v D)
  dsimp only [chooseName] at he
  change E.switch (u*v) _ = E.switch v (E.switch u _)
  rw [he, mul_comm u v,map_mul]
  rfl

end CCO.SafeReadings
