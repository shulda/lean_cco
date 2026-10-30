import CCO.APCharacter.ProperDomains

/-! Finite phase primality on actual original RAW exact domains. Saturation
uses the NONEMPTY resulting meet. The translated domains are strictly above
the WHOLE gate, and original closure separation excludes their finite meet. -/
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace CCO.APCharacter
open RigidGroupoid.Geometry RigidGroupoid.Phase
noncomputable section
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable {H : HomogeneousSource S G} {C : ExactCalculus S} {r : ι} {A : Kernel S r}
namespace SourcePhase
variable (P : SourcePhase S H C A)

theorem phase_primality (cco : SemanticCCO.{u,v,max u v,w} S)
    {i j : ι} (L : List (RawExact.NonemptyExact S i j)) (ε η : Bit)
    (hv : P.validBit i ε) (hw : P.validBit j η)
    (hMeet : TRel.Nonempty (fun x y => ∀ d ∈ L, RawExact.evaluate S d.words x y))
    (hEach : ∀ d ∈ L, ∃ x y, RawExact.evaluate S d.words x y ∧ P.allows (S.colour x y) ε η) :
    ∃ x y, (∀ d ∈ L, RawExact.evaluate S d.words x y) ∧ P.allows (S.colour x y) ε η := by
  classical
  let W := fun x y => ∀ d ∈ L, RawExact.evaluate S d.words x y
  have hW : FullExact S W := ⟨RawExact.exactFamilyMeet S L hMeet,
    RawExact.exactFamilyMeet_relation S L hMeet⟩
  by_contra hgoal
  have hbad : ∀ x y, W x y → ¬P.allows (S.colour x y) ε η := fun x y h hh => hgoal ⟨x,y,h,hh⟩
  have hi : Nonempty (Bridge S A i) := by
    by_contra hn
    obtain ⟨x,y,hxy⟩ := hMeet
    exact hbad x y hxy ((P.allows_actual_iff x y ε η).mpr ⟨hv,hw,fun h _ _ _ => False.elim (hn h)⟩)
  have hj : Nonempty (Bridge S A j) := by
    by_contra hn
    obtain ⟨x,y,hxy⟩ := hMeet
    exact hbad x y hxy ((P.allows_actual_iff x y ε η).mpr ⟨hv,hw,fun _ h _ _ => False.elim (hn h)⟩)
  let b : Reached S A := ⟨i,hi⟩
  let c : Reached S A := ⟨j,hj⟩
  let K := Reached.kernel H C b
  let J := Reached.kernel H C c
  let E (d : RawExact.NonemptyExact S i j) :=
    TRel.comp (TRel.comp K.rel (RawExact.evaluate S d.words)) J.rel
  have eExact (d : RawExact.NonemptyExact S i j) : FullExact S (E d) :=
    C.comp (C.comp K.exact ⟨d,rfl⟩) J.exact
  have eLeft (d : RawExact.NonemptyExact S i j) : TRel.comp K.rel (E d) = E d := by
    dsimp [E]
    rw [← TRel.comp_assoc,← TRel.comp_assoc,K.comp_self]
  have eRight (d : RawExact.NonemptyExact S i j) : TRel.comp (E d) J.rel = E d := by
    dsimp [E]
    rw [TRel.comp_assoc,J.comp_self]
  let D := TRel.comp (TRel.comp K.rel W) J.rel
  have hD : FullExact S D := C.comp (C.comp K.exact hW) J.exact
  have hLeft : TRel.comp K.rel D = D := by
    dsimp [D]
    rw [← TRel.comp_assoc,← TRel.comp_assoc,K.comp_self]
  have hRight : TRel.comp D J.rel = D := by
    dsimp [D]
    rw [TRel.comp_assoc,J.comp_self]
  have wrong := P.wrong_saturate b c (η-ε) W (P.wrong_of_not_allows hi hj ε η hv hw W hbad)
  obtain ⟨F,hF⟩ := P.wrong_exact_single_bridge cco b c (η-ε) D hD hLeft hRight wrong
  let KI : RawExact.NonemptyExact S i i := Classical.choose K.exact
  let JI : RawExact.NonemptyExact S j j := Classical.choose J.exact
  have hKI : RawExact.evaluate S KI.words = K.rel := Classical.choose_spec K.exact
  have hJI : RawExact.evaluate S JI.words = J.rel := Classical.choose_spec J.exact
  have dist := RawExact.fullExact_saturation_meet_distribution_of_CCO S H cco KI JI L hMeet
  rw [hKI,hJI] at dist
  have hIntersection : (fun x y => ∀ d ∈ L, E d x y) = F.rel := dist.symm.trans hF
  have hFle (d : RawExact.NonemptyExact S i j) (hd : d ∈ L) :
      ∀ x y, F.rel x y → E d x y := by
    intro x y hf
    have hh := Eq.mpr (congrFun (congrFun hIntersection x) y) hf
    exact hh d hd
  letI := Reached.groupoid H C (A := A)
  have hWrongF : P.character.value F ≠ η-ε := by
    obtain ⟨x,y,hxy⟩ := F.exact.nonempty S
    have hDxy : D x y := by rw [hF]; exact hxy
    obtain ⟨R,hR,hχ⟩ := wrong x y hDxy
    have he : R = F := R.eq_of_common_real_pair H F hR hxy
    exact he ▸ hχ
  let U (d : {d : RawExact.NonemptyExact S i j // d ∈ L}) : ProperDomain (H := H) (C := C) b := {
    rel := TRel.comp (E d.val) F.inv.rel
    exact := C.comp (eExact d.val) F.inv.exact
    contains := by
      intro x y hxy
      rw [← F.source] at hxy
      obtain ⟨z,hxz,hyz⟩ := hxy
      exact ⟨z,hFle d.val d.property x z hxz,hyz⟩
    saturated := ⟨by
      change TRel.comp K.rel (TRel.comp (E d.val) F.inv.rel) = _
      rw [← TRel.comp_assoc,eLeft],
      by
      change TRel.comp (TRel.comp (E d.val) F.inv.rel) K.rel = _
      rw [TRel.comp_assoc,F.inv.right]⟩
    outside := by
      by_contra hn
      have hle : ∀ x y, TRel.comp (E d.val) F.inv.rel x y → K.rel x y := by
        intro x y hxy
        exact Classical.byContradiction fun hk => hn ⟨x,y,hxy,hk⟩
      obtain ⟨x,y,hxy,hallow⟩ := hEach d.val d.property
      have hE : E d.val x y := ⟨y,⟨x,K.setoid.refl x,hxy⟩,J.setoid.refl y⟩
      obtain ⟨z,hzy⟩ := F.exact.coserial S H y
      have hk : K.rel x z := hle x z ⟨y,hE,hzy⟩
      have hf : F.rel x y := by rw [← F.left]; exact ⟨z,hk,hzy⟩
      have hgood := hallow.2.2 x y rfl hi hj F hf
      apply hWrongF
      apply eq_sub_iff_add_eq.mpr
      simpa only [add_comm] using hgood.symm
  }
  let UL := L.attach.map U
  let Q := ProperDomain.meetList P cco b UL
  obtain ⟨x,y,hxy,hnK⟩ := Q.outside
  have hAll : ∀ d ∈ L, TRel.comp (E d) F.inv.rel x y := by
    intro d hd
    have hm : U ⟨d,hd⟩ ∈ UL := List.mem_map.mpr ⟨⟨d,hd⟩,List.mem_attach _ _,rfl⟩
    have hh := Eq.mp (congrFun (congrFun (ProperDomain.meetList_relation P cco UL) x) y) hxy
    exact hh (U ⟨d,hd⟩) hm
  obtain ⟨z,hyz⟩ := F.exact.serial S H y
  have hEvery : ∀ d ∈ L, E d x z := by
    intro d hd
    obtain ⟨q,hxq,hyq⟩ := hAll d hd
    have hJ : J.rel q z := by rw [← F.target]; exact ⟨y,hyq,hyz⟩
    rw [← eRight d]
    exact ⟨q,hxq,hJ⟩
  have hf : F.rel x z := Eq.mp (congrFun (congrFun hIntersection x) z) hEvery
  apply hnK
  rw [← F.source]
  exact ⟨z,hf,hyz⟩

end SourcePhase
end
end CCO.APCharacter
