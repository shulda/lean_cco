import CCO.HiddenSAPReadings.RealSplitting

/-! The finite-family construction is instantiated on EVERY actual old
real source position and EVERY actual proper source position, including
orphan positions and coincident proper images. All existing hidden data
are preserved by actual pair motions, with quotient values fixed. -/
universe u v w r z
namespace CCO.HiddenSAPReadings
open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.TypedOrbitFrames
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G)
variable {P : Type z} (f : P → OriginalCompletedNamedCarrier S H)

def IsRealPosition (p : P) : Prop := ∃ x : Sigma X, f p = .inl x
abbrev RealPosition := {p : P // IsRealPosition S H f p}
abbrev ProperPosition := {p : P // ¬ IsRealPosition S H f p}
def realPositionValue (p : RealPosition S H f) : Sigma X := p.property.choose
theorem realPositionValue_eq (p : RealPosition S H f) :
    f p.val = .inl (realPositionValue S H f p) := p.property.choose_spec

theorem properPosition_request (p : ProperPosition S H f) :
    ∃ q : AnchorRequest S H,
      originalCompletedNamedHiddenNode S H q.2.1 q.2.2 = f p.val := by
  cases he : f p.val with
  | inl x => exact False.elim (p.property ⟨x,he⟩)
  | inr x =>
      obtain ⟨i,D,q,hq⟩ := original_completed_hidden_value_has_named_witness S H x
      exact ⟨⟨i,D,q⟩,hq.symm⟩

def properPositionRequest (p : ProperPosition S H f) : AnchorRequest S H :=
  (properPosition_request S H f p).choose
theorem properPositionRequest_eq (p : ProperPosition S H f) :
    originalCompletedNamedHiddenNode S H (properPositionRequest S H f p).2.1
      (properPositionRequest S H f p).2.2 = f p.val :=
  (properPosition_request S H f p).choose_spec

structure SplitAssignment (A : Set (Sigma X)) where
  point : P → OriginalCompletedNamedCarrier S H
  world : FiniteInduced (X := X)
  contains_original : A ⊆ world.vertices
  sort_eq : ∀ p, originalCompletedVertexSort S H (point p) = originalCompletedVertexSort S H (f p)
  proper_fixed : ∀ p, ¬ IsRealPosition S H f p → point p = f p
  real_injective : ∀ p q, IsRealPosition S H f p → IsRealPosition S H f q →
    point p = point q → p = q
  pair_motion : ∀ p q, f p ≠ f q → ∃ g : G,
    originalCompletedNamedAct S H g (f p) = point p ∧
      originalCompletedNamedAct S H g (f q) = point q
  representative : ProperPosition S H f → Sigma X
  representatives_injective : Function.Injective representative
  representative_class : ∀ p, representative p ∈
    anchorRepresentatives S H (properPositionRequest S H f p)
  representatives_in_world : ∀ p, representative p ∈ world.vertices
  real_in_world : ∀ p x, point p = .inl x → x ∈ world.vertices
  real_representative_disjoint : ∀ p x, point p = .inl x →
    ∀ q, x ≠ representative q

include H in
theorem split_finite_assignment [Finite P] (sap : AgeSAP S)
    (A : Set (Sigma X)) (hA : A.Finite) : Nonempty (SplitAssignment S H f A) := by
  classical
  let I := RealPosition S H f
  let J := ProperPosition S H f
  let sort : I → ι := fun p => (realPositionValue S H f p).1
  let old : ∀ p, X (sort p) := fun p => (realPositionValue S H f p).2
  obtain ⟨fresh,anchor,world,hA',hFresh,hAnch,hClass,hDisj,hFreshWorld,hAnchWorld,hCoord,hFine,hMixed⟩ :=
    typed_real_sort_splitting S H sap sort old (properPositionRequest S H f) A hA
  let point : P → OriginalCompletedNamedCarrier S H := fun p =>
    if hp : IsRealPosition S H f p then .inl ⟨sort ⟨p,hp⟩,fresh ⟨p,hp⟩⟩ else f p
  have hReal (p : I) : point p.val = .inl ⟨sort p,fresh p⟩ := by
    dsimp only [point]
    rw [dif_pos p.property]
  have hProper (p : J) : point p.val = f p.val := dif_neg p.property
  have hMixedMotion (p : I) (q : J) : ∃ g : G,
      originalCompletedNamedAct S H g (f p.val) = point p.val ∧
        originalCompletedNamedAct S H g (f q.val) = point q.val := by
    let req := properPositionRequest S H f q
    obtain ⟨R,hR⟩ := original_completed_distinct_pair_binary_exists S H sap
      (.inl ⟨sort p,old p⟩) (originalCompletedNamedHiddenNode S H req.2.1 req.2.2)
      (by intro h; cases h)
    have hR' := (hMixed p q R).mpr hR
    obtain ⟨g,hgp,hgq⟩ := same_binary_motion S H R hR hR'
    refine ⟨g,?_,?_⟩
    · rw [realPositionValue_eq S H f p,hReal]
      exact hgp
    · rw [hProper,← properPositionRequest_eq S H f q]
      exact hgq
  refine ⟨{
    point := point
    world := world
    contains_original := hA'
    sort_eq := ?_
    proper_fixed := fun p hp => hProper ⟨p,hp⟩
    real_injective := ?_
    pair_motion := ?_
    representative := anchor
    representatives_injective := hAnch
    representative_class := hClass
    representatives_in_world := hAnchWorld
    real_in_world := ?_
    real_representative_disjoint := ?_ }⟩
  · intro p
    by_cases hp : IsRealPosition S H f p
    · rw [hReal ⟨p,hp⟩,realPositionValue_eq S H f ⟨p,hp⟩]
      rfl
    · rw [hProper ⟨p,hp⟩]
  · intro p q hp hq he
    rw [hReal ⟨p,hp⟩,hReal ⟨q,hq⟩] at he
    exact congrArg Subtype.val (hFresh (Sum.inl.inj he))
  · intro p q hpq
    by_cases hp : IsRealPosition S H f p
    · by_cases hq : IsRealPosition S H f q
      · let pi : I := ⟨p,hp⟩
        let qi : I := ⟨q,hq⟩
        have hne : (⟨sort pi,old pi⟩ : Sigma X) ≠ ⟨sort qi,old qi⟩ := by
          intro he
          exact hpq ((realPositionValue_eq S H f pi).trans
            ((congrArg Sum.inl he).trans (realPositionValue_eq S H f qi).symm))
        obtain ⟨a,ha⟩ := S.some_colour_of_ne (old pi) (old qi) hne
        obtain ⟨g,hgp,hgq⟩ := S.pair_homogeneous_of_homogeneous H (old pi) (fresh pi)
          (old qi) (fresh qi) (ha.trans (hFine pi qi a ha).symm)
        refine ⟨g,?_,?_⟩
        · rw [realPositionValue_eq S H f pi,hReal pi]
          exact congrArg (fun x => (Sum.inl ⟨sort pi,x⟩ : OriginalCompletedNamedCarrier S H)) hgp
        · rw [realPositionValue_eq S H f qi,hReal qi]
          exact congrArg (fun x => (Sum.inl ⟨sort qi,x⟩ : OriginalCompletedNamedCarrier S H)) hgq
      · exact hMixedMotion ⟨p,hp⟩ ⟨q,hq⟩
    · by_cases hq : IsRealPosition S H f q
      · obtain ⟨g,hgq,hgp⟩ := hMixedMotion ⟨q,hq⟩ ⟨p,hp⟩
        exact ⟨g,hgp,hgq⟩
      · exact ⟨1,(original_completed_named_act_one S H _).trans (hProper ⟨p,hp⟩).symm,
          (original_completed_named_act_one S H _).trans (hProper ⟨q,hq⟩).symm⟩
  · intro p x hx
    by_cases hp : IsRealPosition S H f p
    · rw [hReal ⟨p,hp⟩] at hx
      exact (Sum.inl.inj hx) ▸ hFreshWorld ⟨p,hp⟩
    · exact False.elim (hp ⟨x,(hProper ⟨p,hp⟩).symm.trans hx⟩)
  · intro p x hx q
    by_cases hp : IsRealPosition S H f p
    · rw [hReal ⟨p,hp⟩] at hx
      exact (Sum.inl.inj hx) ▸ hDisj ⟨p,hp⟩ q
    · exact False.elim (hp ⟨x,(hProper ⟨p,hp⟩).symm.trans hx⟩)

end
end CCO.HiddenSAPReadings
