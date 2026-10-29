import CCO.HKNReservoir.RealizedRanges
import AllThoseEPPA.TreeLikeInfiniteCopiesAmbientPostcompose

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

/-- Actual closed SAP aligns the whole right completion, while retaining
all old left points and every fine colour already put on them. -/
theorem align_realized_span {I X Y : Type (max v w)}
    [Finite I] [Finite X] [Finite Y]
    {C : Structure L I} {D₁ : Structure L X} {D₂ : Structure L Y}
    (f : Structure.Embedding act C D₁) (g : Structure.Embedding act C D₂)
    (e₁ : Structure.Embedding act D₁ N) (e₂ : Structure.Embedding act D₂ N) :
    ∃ r : Structure.Embedding act D₂ N,
      e₁.lang * f.lang = r.lang * g.lang ∧
      (∀ c, e₁ (f c) = r (g c)) ∧
      (∀ x y, e₁ x = r y ↔ ∃ c, f c = x ∧ g c = y) := by
  classical
  obtain ⟨σ,hσ⟩ := ambientLift S H R B hB Δ
    (e₁.lang * f.lang * g.lang⁻¹ * e₂.lang⁻¹)
  let e₂' := (σ.toEmbedding act).comp e₂
  let u := e₁.comp f
  let z := e₂'.comp g
  have hlang : u.lang = z.lang := by
    change e₁.lang * f.lang = (σ.lang * e₂.lang) * g.lang
    rw [hσ]
    simp [mul_assoc]
  let C₀ := namedRange S H R B u.toFun
  let P₁ := namedRange S H R B e₁.toFun
  let P₂ := namedRange S H R B e₂'.toFun
  have hsub : C₀ ⊆ P₁ := by
    intro a ha
    obtain ⟨c,hc⟩ := (mem_namedRange S H R B u.toFun a).mp ha
    exact (mem_namedRange S H R B e₁.toFun a).mpr ⟨f c,hc⟩
  let d₁ : NamedEmbedding S H R B C₀ P₁ :=
    ⟨⟨fun a => ⟨a.val,hsub a.property⟩,fun _ _ h => Subtype.ext (congrArg (fun z : ↥P₁ => z.val) h)⟩,
      fun _ => rfl,fun _ _ => rfl⟩
  have hP₂ (c : I) : (z c).down ∈ P₂ :=
    (mem_namedRange S H R B e₂'.toFun _).mpr ⟨g c,rfl⟩
  let d₂ := rangeCorrespondence S H R B hB Δ u z hlang P₂ hP₂
  obtain ⟨k,hbase,hcross⟩ := Actual.closed_span_fix_left S H R B C₀ P₁ P₂
    (namedRange_closed S H R B hB Δ u)
    (namedRange_closed S H R B hB Δ e₁)
    (namedRange_closed S H R B hB Δ e₂') d₁ d₂
  let r := ((namedAut S H R B hB Δ k).toEmbedding act).comp e₂'
  have hr (y : Y) : (r y).down = k.val (e₂' y).down := rfl
  have hcomm (c : I) : e₁ (f c) = r (g c) := by
    apply ULift.ext
    let a : ↥C₀ := ⟨(u c).down,(mem_namedRange S H R B u.toFun _).mpr ⟨c,rfl⟩⟩
    have ha := hbase a
    have hd := rangeCorrespondence_apply S H R B hB Δ u z hlang P₂ hP₂ c
    change (d₂.toEmbedding a).val = (z c).down at hd
    change k.val (d₂.toEmbedding a).val = (u c).down at ha
    rw [hd] at ha
    exact ha.symm
  refine ⟨r,?_,hcomm,?_⟩
  · change e₁.lang * f.lang = (1 * (σ.lang * e₂.lang)) * g.lang
    change e₁.lang * f.lang = (σ.lang * e₂.lang) * g.lang at hlang
    simpa only [one_mul] using hlang
  · intro x y
    constructor
    · intro he
      let l : ↥P₁ := ⟨(e₁ x).down,(mem_namedRange S H R B e₁.toFun _).mpr ⟨x,rfl⟩⟩
      let p : ↥P₂ := ⟨(e₂' y).down,(mem_namedRange S H R B e₂'.toFun _).mpr ⟨y,rfl⟩⟩
      obtain ⟨a,ha₁,ha₂⟩ := (hcross l p).mp (congrArg ULift.down he)
      obtain ⟨c,hc⟩ := (mem_namedRange S H R B u.toFun a.val).mp a.property
      have hca : (⟨(u c).down,(mem_namedRange S H R B u.toFun _).mpr ⟨c,rfl⟩⟩ : ↥C₀) = a := Subtype.ext hc
      have hd := rangeCorrespondence_apply S H R B hB Δ u z hlang P₂ hP₂ c
      rw [hca] at hd
      refine ⟨c,e₁.injective (ULift.ext _ _ ?_),e₂'.injective (ULift.ext _ _ ?_)⟩
      · exact hc.trans (congrArg Subtype.val ha₁)
      · exact hd.symm.trans (congrArg Subtype.val ha₂)
    · rintro ⟨c,rfl,rfl⟩
      exact hcomm c

end
end CCO.HKNReservoir
