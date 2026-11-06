import CCO.HiddenSAPReadings.Anchors
import CCO.HiddenSAPReadings.CompleteBaseClones
import Mathlib.Data.Fin.Tuple.Basic

/-! Finite anchors are chosen in the literal infinite proper fibres.
Original SAP then separates all formal real positions while fixing ONE
complete actual old frame. Colliding formal positions do not create extra
actual base points. No hidden SAP, CCO or completion provider is used. -/
universe u v w r z
namespace CCO.HiddenSAPReadings
open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.TypedOrbitFrames
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)

theorem finite_fresh_choices {V : Type*} {n : ℕ} (F : Fin n → Set V)
    (hF : ∀ i, (F i).Infinite) (Z : Set V) (hZ : Z.Finite) :
    ∃ f : Fin n → V, Function.Injective f ∧ ∀ i, f i ∈ F i ∧ f i ∉ Z := by
  classical
  induction n with
  | zero => exact ⟨Fin.elim0,fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩
  | succ n ih =>
      obtain ⟨f,hf,hfP⟩ := ih (fun i => F i.castSucc) (fun i => hF i.castSucc)
      obtain ⟨x,hx,hxZ⟩ := (hF (Fin.last n)).exists_notMem_finite
        (hZ.union (Set.finite_range f))
      have hxnot : x ∉ Set.range f := fun h => hxZ (Or.inr h)
      refine ⟨Fin.snoc f x,Fin.snoc_injective_of_injective hf hxnot,?_⟩
      intro i
      induction i using Fin.lastCases with
      | cast i => simpa only [Fin.snoc_castSucc] using hfP i
      | last => exact ⟨by simpa only [Fin.snoc_last] using hx,
          fun h => hxZ (Or.inl (by simpa only [Fin.snoc_last] using h))⟩

abbrev AnchorRequest := Σ i : ι, Σ D : OriginalNamedHiddenCoordinate S H i, Quotient D.val.val

def anchorRepresentatives (q : AnchorRequest S H) : Set (Sigma X) :=
  {p | ∃ a : X q.1, p = ⟨q.1,a⟩ ∧ Quotient.mk q.2.1.val.val a = q.2.2}

include H sap in
theorem proper_fibre_infinite {i : ι} (D : OriginalNamedHiddenCoordinate S H i)
    (q : Quotient D.val.val) : {a : X i | Quotient.mk D.val.val a = q}.Infinite := by
  obtain ⟨x,rfl⟩ := Quotient.exists_rep q
  have hi := original_nonidentity_finite_meet_class_infinite S H sap
    (fun _ : Fin 1 => D.val) (fun _ => D.property.1) x
  apply hi.mono
  intro y hy
  exact Quotient.sound (D.val.val.symm (hy 0))

include H sap in
theorem anchorRepresentatives_infinite (q : AnchorRequest S H) :
    (anchorRepresentatives S H q).Infinite := by
  have hi := (proper_fibre_infinite S H sap q.2.1 q.2.2).image
    (f := Sigma.mk q.1) (by intro a _ b _ h; exact sigma_mk_injective h)
  apply hi.mono
  rintro _ ⟨a,ha,rfl⟩
  exact ⟨a,rfl,ha⟩

include H sap in
theorem finite_actual_anchors {J : Type z} [Finite J]
    (q : J → AnchorRequest S H) (Z : Set (Sigma X)) (hZ : Z.Finite) :
    ∃ f : J → Sigma X, Function.Injective f ∧
      ∀ j, f j ∈ anchorRepresentatives S H (q j) ∧ f j ∉ Z := by
  classical
  letI : Fintype J := Fintype.ofFinite J
  let e := Fintype.equivFin J
  obtain ⟨f,hf,hfP⟩ := finite_fresh_choices
    (fun i => anchorRepresentatives S H (q (e.symm i)))
    (fun i => anchorRepresentatives_infinite S H sap _) Z hZ
  exact ⟨f ∘ e,hf.comp e.injective,fun j => by simpa using hfP (e j)⟩

/-- The auxiliary old graph records exactly the actual old fine colours
of its current image. None remains a missing diversity edge. -/
def actualImageDiagram {V : Type*} [Finite V] (f : V → Sigma X) : PartialDiagram S V where
  finite_type := inferInstance
  vertexSort v := (f v).1
  edge v w _ := S.colour (f v).2 (f w).2
  edge_reverse v w _ a := S.colour_swap (f v).2 (f w).2 a

def actualImageHom {V : Type*} [Finite V] (f : V → Sigma X) :
    DiagramHom (actualImageDiagram S f) where
  point v := (f v).2
  preserves_edge _ _ _ _ h := h

include H sap in
/-- ONE complete actual frame is fixed, including the original finite
target. Only diversity pairs are prescribed between colliding formal
positions; the accepted SAP induction separates them all. -/
theorem split_real_family_over_frame {I : Type z} [Finite I]
    (sort : I → ι) (old : ∀ i, X (sort i))
    (A B : Set (Sigma X)) (hA : A.Finite) (hB : B.Finite)
    (hAvoid : ∀ i, (⟨sort i,old i⟩ : Sigma X) ∉ B) :
    ∃ fresh : ∀ i, X (sort i),
      Function.Injective (fun i => (⟨sort i,fresh i⟩ : Sigma X)) ∧
      (∀ i, (⟨sort i,fresh i⟩ : Sigma X) ∉ A ∪ B) ∧
      (∀ i (b : B), S.colour (fresh i) b.val.2 = S.colour (old i) b.val.2) ∧
      (∀ i j (a : S.Atom (sort i) (sort j)), S.atomRel a (old i) (old j) →
        S.atomRel a (fresh i) (fresh j)) := by
  classical
  let frame := A ∪ B
  have hframe : frame.Finite := hA.union hB
  letI : Finite frame := hframe.to_subtype
  let f : I ⊕ frame → Sigma X := Sum.elim (fun i => ⟨sort i,old i⟩) Subtype.val
  let D := actualImageDiagram S f
  let f₀ := actualImageHom S f
  let pins : Set (I ⊕ frame) := Set.range Sum.inr
  have hPin : ∀ u ∈ pins, ∀ v ∈ pins, f₀.image u = f₀.image v → u = v := by
    rintro _ ⟨u,rfl⟩ _ ⟨v,rfl⟩ he
    exact congrArg Sum.inr (Subtype.ext he)
  obtain ⟨g,hg,hfixed,_⟩ := CompleteBaseClones.injectivize H sap f₀ pins hPin ∅ Set.finite_empty
  let fresh : ∀ i, X (sort i) := fun i => g.point (.inl i)
  have hFix (b : frame) : g.point (.inr b) = b.val.2 := by
    have h := hfixed (.inr b) ⟨b,rfl⟩
    exact sigma_mk_injective h
  refine ⟨fresh,?_,?_,?_,?_⟩
  · intro i j he
    exact Sum.inl.inj (hg he)
  · intro i hi
    let b : frame := ⟨⟨sort i,fresh i⟩,hi⟩
    have he : g.image (.inl i) = g.image (.inr b) := by
      change (⟨sort i,fresh i⟩ : Sigma X) = ⟨b.val.1,g.point (.inr b)⟩
      rw [hFix]
    cases hg he
  · intro i b
    let bf : frame := ⟨b.val,Or.inr b.property⟩
    obtain ⟨a,ha⟩ := S.some_colour_of_ne (old i) b.val.2
      (fun h => hAvoid i (h ▸ b.property))
    have h := g.preserves_edge (.inl i) (.inr bf) (by intro h; cases h) a ha
    rw [hFix bf] at h
    exact h.trans ha.symm
  · intro i j a ha
    have hij : i ≠ j := by
      intro h
      subst j
      exact S.atomRel_ne ha rfl
    exact g.preserves_edge (.inl i) (.inl j) (fun h => hij (Sum.inl.inj h)) a ha

end
end CCO.HiddenSAPReadings
