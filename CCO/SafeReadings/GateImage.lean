import CCO.SafeReadings.GatePC

universe u v w
namespace CCO.SafeReadings
open Selectors
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι} {Q : Family S}

theorem gate_idempotent (C : MenuCalculus S Q) {F J : Family S}
    (hF : Filter S Q F) (hJ : Current S Q J) (hV : Visible S F J)
    {D : S.Menu i j} (hD : (⟨i,j,D⟩ : TaggedMenu S) ∈ J) :
    gate S F (gate S F D) = gate S F D := by
  obtain ⟨a,ha⟩ := gate_nonempty S C hF hJ hV hD
  simpa only [Set.inter_self] using
    gate_heredity S F (gate_subset S F D) ⟨a,ha,ha⟩

theorem gateImage_eq_fixed (C : MenuCalculus S Q) {F J : Family S}
    (hF : Filter S Q F) (hJ : Current S Q J) (hV : Visible S F J) :
    gateImage S F J = fixedFamily S F J := by
  apply Set.Subset.antisymm
  · rintro _ ⟨⟨i,j,D⟩,hD,rfl⟩
    exact ⟨gate_current S C hF hJ hV hD,gate_idempotent S C hF hJ hV hD⟩
  · rintro ⟨i,j,D⟩ ⟨hD,hFix⟩
    exact ⟨⟨i,j,D⟩,hD,by simp only [gateTag,hFix]⟩

theorem gate_fixes_singleton (C : MenuCalculus S Q) {F J : Family S}
    (hF : Filter S Q F) (hJ : Current S Q J) (hV : Visible S F J)
    (a : S.Atom i j) : gate S F ({a} : S.Menu i j) = {a} := by
  obtain ⟨b,hb⟩ := gate_nonempty S C hF hJ hV (hJ.singleton a)
  have hba : b = a := Set.mem_singleton_iff.mp hb.1
  subst b
  exact Set.Subset.antisymm (gate_subset S F _) (by intro b hb'; simpa using hb' ▸ hb)

/-- C18: the actual image remains a current evaluated Q family. -/
theorem gateImage_current (C : MenuCalculus S Q) {F J : Family S}
    (hF : Filter S Q F) (hJ : Current S Q J) (hV : Visible S F J) :
    Current S Q (gateImage S F J) := by
  rw [gateImage_eq_fixed S C hF hJ hV]
  refine ⟨fun _ h => hJ.member h.1,?_,?_,?_⟩
  · intro i j a
    exact ⟨hJ.singleton a,gate_fixes_singleton S C hF hJ hV a⟩
  · rintro ⟨i,j,D⟩ ⟨hD,hFix⟩
    refine ⟨hJ.opposite hD,?_⟩
    change gate S F (S.opposite D) = S.opposite D
    rw [gate_opposite S hF,hFix]
  · intro i j D E hD hE hED
    refine ⟨hJ.downward hD.1 hE hED,?_⟩
    obtain ⟨a,ha⟩ := C.nonempty hE
    have hMeet : (E ∩ gate S F D).Nonempty := ⟨a,ha,by rw [hD.2]; exact hED ha⟩
    rw [gate_heredity S F hED hMeet,hD.2]
    exact Set.inter_eq_left.mpr hED

theorem gateImage_subset (C : MenuCalculus S Q) {F J : Family S}
    (hF : Filter S Q F) (hJ : Current S Q J) (hV : Visible S F J) :
    gateImage S F J ⊆ J := by
  rw [gateImage_eq_fixed S C hF hJ hV]
  exact fun _ h => h.1

/-- A proper active trace removes the original current menu from the image. -/
theorem gateImage_strict (C : MenuCalculus S Q) {F J : Family S}
    (hF : Filter S Q F) (hJ : Current S Q J) (hV : Visible S F J)
    {D A : S.Menu i j} (hD : (⟨i,j,D⟩ : TaggedMenu S) ∈ J)
    (hA : (⟨i,j,A⟩ : TaggedMenu S) ∈ F) (hAD : (A ∩ D).Nonempty)
    (hProper : ¬D ⊆ A) : gateImage S F J ⊂ J := by
  refine Set.ssubset_iff_subset_ne.mpr ⟨gateImage_subset S C hF hJ hV,?_⟩
  intro heq
  have hFix : gate S F D = D := by
    have hm : (⟨i,j,D⟩ : TaggedMenu S) ∈ gateImage S F J := heq.symm ▸ hD
    rw [gateImage_eq_fixed S C hF hJ hV] at hm
    exact hm.2
  apply hProper
  rw [← hFix]
  exact gate_subset_active S hA hAD

/-- C18's cardinal measure is the actual finite tagged-menu image. -/
theorem gateImage_card_lt (C : MenuCalculus S Q) {F J : Family S}
    (hF : Filter S Q F) (hJ : Current S Q J) (hV : Visible S F J)
    {D A : S.Menu i j} (hD : (⟨i,j,D⟩ : TaggedMenu S) ∈ J)
    (hA : (⟨i,j,A⟩ : TaggedMenu S) ∈ F) (hAD : (A ∩ D).Nonempty)
    (hProper : ¬D ⊆ A) : Nat.card (gateImage S F J) < Nat.card J :=
  Set.ncard_lt_ncard (gateImage_strict S C hF hJ hV hD hA hAD hProper)

/-- The genuine original visible gate, packaged for finite composition. -/
def gateContraction (C : MenuCalculus S Q)
    (hPoint : S.RealPointGluing) (hEdge : S.RealEdgeGluing)
    {F J : Family S} (hF : Filter S Q F) (hJ : Current S Q J)
    (hV : Visible S F J) : Contraction S J (gateImage S F J) where
  toFun D := gate S F D
  maps := by intro i j D hD; exact ⟨⟨i,j,D⟩,hD,rfl⟩
  conservative _ := gate_subset S F _
  opposite _ := gate_opposite S hF _
  heredity _ _ hED hm := gate_heredity S F hED hm
  pc hA hB hD hPC := gate_preserves_PC S C hPoint hEdge hF hJ hV hA hB hD hPC

end CCO.SafeReadings
