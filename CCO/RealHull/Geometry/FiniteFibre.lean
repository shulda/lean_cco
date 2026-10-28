import CCO.RealHull.Geometry.FibreFixer
import CCO.RealHull.Geometry.FibreTriangle
import CCO.RealHull.Geometry.ClassSizes
import CCO.ParityHasse.Relative.TwoSheet

/-! One full INTERNAL cover globalises the finite actual fibre. The clearly
named conditional core below consumes inherited fibre CCO and the independently
proved original square-localisation law; final source exports discharge both.
No intermediate equivalence is globalised in this proof. -/
universe v w t
namespace CCO.RealHull.Geometry
open ParityHasse.Original
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))

def SpokeLocalisation : Prop :=
  ∀ (R : Support S) (P : Finset (Atom S)), P.Nonempty →
    (∀ p ∈ P, Fixed S R p) → ∀ c : Atom S,
    (∀ p ∈ P, c ∈ square S p) →
    (∀ d : Atom S, d ∈ square S c → (∀ p ∈ P, d ∈ square S p) → d ∈ R.val) →
    ∀ p ∈ P, prod S {some p} {some c} = {some p}

variable [DecidableEq M] (A : Finset M) (q : ↥A → Atom S)
variable [Nonempty (FibreSet S A q)]

def fibreRestriction (R : Support S) : ColourEq (fibreSource S A q) () :=
  ⟨Setoid.comap (fun x : FibreSet S A q => x.val) (supportEquiv S R).val,by
    intro x y x' y' hc
    have ho := (inducedColour_eq_iff S () (FibreSet S A q) x y x' y').mp hc
    change (col S x.val y.val ∈ plus S R.val) ↔ (col S x'.val y'.val ∈ plus S R.val)
    change col S x.val y.val = col S x'.val y'.val at ho
    rw [ho]⟩

variable {G : Type t} [Group G] [MulAction G M]

/-- The finite internal Hasse/size result is available BEFORE globalisation. -/
theorem finite_fibre_size_of_CCO (H : HomogeneousSource S G)
    (fcco : SemanticCCO.{0,v,0,w} (fibreSource S A q))
    [Finite (FibreSet S A q)] :
    ∃ n : Nat, Nat.card (FibreSet S A q) = 2^n ∧ n ≤ Nat.card (Atom S) := by
  classical
  obtain ⟨x⟩ := ‹Nonempty (FibreSet S A q)›
  obtain ⟨n,hn,hbound⟩ := finite_sort_size_power_two (fibreSource S A q) ()
    (fibre_homogeneous S A q H) fcco x
  letI := S.finiteAtom () ()
  exact ⟨n,hn,le_trans hbound (Nat.card_le_card_of_injective
    (fun c : InducedAtom S () (FibreSet S A q) => c.val) Subtype.val_injective)⟩

/-- The core uses ONE full internal index-two cover. Original triangles are
transferred over the same whole anchor; original square localisation then
contradicts the cover layer. Its two providers are explicit until instantiated.
-/
theorem finite_fibre_palette_eq_of_localisation (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S)
    (fcco : SemanticCCO.{0,v,0,w} (fibreSource S A q)) (loc : SpokeLocalisation S)
    [Finite (FibreSet S A q)] (hA : A.Nonempty) :
    ∀ c : Atom S, (∀ a : ↥A, c ∈ square S (q a)) →
      c ∈ (fibreSpokeFixer S A q H).val := by
  classical
  let D := fibreSource S A q
  let R := fibreSpokeFixer S A q H
  let Y := fibreRestriction S A q R
  let P : Finset (Atom S) := Finset.univ.image q
  have hpP (a : ↥A) : q a ∈ P := Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
  have hP : P.Nonempty := by
    obtain ⟨a,ha⟩ := hA
    exact ⟨q ⟨a,ha⟩,hpP _⟩
  have hfixP : ∀ p ∈ P, Fixed S R p := by
    intro p hp
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hp
    exact fibreSpokeFixer_fixed S A q H a
  intro c hc
  by_contra hcR
  obtain ⟨xc,yc,hxyc⟩ := fibre_pair_realize S A q H cco c hc
  have hYtop : Y < (⊤ : ColourEq D ()) := by
    apply lt_of_le_not_ge le_top
    intro htop
    have hh : Y xc yc := htop (show (⊤ : ColourEq D ()) xc yc from trivial)
    change col S xc.val yc.val ∈ plus S R.val at hh
    rw [hxyc,some_mem_plus] at hh
    exact hcR hh
  obtain ⟨U,hYU,_⟩ := hYtop.exists_covby_le
  have hdiff : ∃ x y : FibreSet S A q, U x y ∧ ¬Y x y := by
    by_contra hn
    apply hYU.lt.not_ge
    intro x y hU
    by_contra hY
    exact hn ⟨x,y,hU,hY⟩
  obtain ⟨x,y,hUxy,hnotY⟩ := hdiff
  have hne : x.val ≠ y.val := by
    intro he
    exact hnotY (by change supportEquiv S R x.val y.val; rw [he])
  obtain ⟨b,hb⟩ := col_some_of_ne S hne
  have hbR : b ∉ R.val := by
    intro hR
    apply hnotY
    change col S x.val y.val ∈ plus S R.val
    rw [hb,some_mem_plus]
    exact hR
  let bI : InducedAtom S () (FibreSet S A q) := ⟨b,x,y,hb⟩
  have htwo (z : FibreSet S A q) : relativeIndex Y.val U.val z = 2 := by
    letI : Finite (RelativeClass Y.val U.val z) := by unfold RelativeClass; infer_instance
    exact full_relative_hasse D (fibre_homogeneous S A q H) fcco Y U hYU z
  have hodd (u v : FibreSet S A q) (huv : col S u.val v.val = some b) :
      ParityHasse.Relative.odd Y.val U.val u v := by
    have hcol : D.colour (i := ()) (j := ()) x y = D.colour (i := ()) (j := ()) u v :=
      (inducedColour_eq_iff S () _ x y u v).mpr (hb.trans huv.symm)
    refine ⟨(U.property x y u v hcol).mp hUxy,?_⟩
    intro hY
    apply hbR
    change col S u.val v.val ∈ plus S R.val at hY
    rwa [huv,some_mem_plus] at hY
  have hbT : ∀ a : ↥A, b ∈ square S (q a) :=
    (fibre_palette_iff S A q H cco b).mp ⟨x,y,hb⟩
  have hbP : ∀ p ∈ P, b ∈ square S p := by
    intro p hp
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hp
    exact hbT a
  have hsquare : ∀ d : Atom S, d ∈ square S b →
      (∀ p ∈ P, d ∈ square S p) → d ∈ R.val := by
    intro d hd hdP
    have hdT : ∀ a : ↥A, d ∈ square S (q a) := fun a => hdP (q a) (hpP a)
    let dI : InducedAtom S () (FibreSet S A q) :=
      ⟨d,fibre_pair_realize S A q H cco d hdT⟩
    obtain ⟨u,v,z,huv,hvz,huz⟩ := original_triangle_in_fibre S A q H cco bI bI dI
      ((mem_row S b b d).mp hd)
    have huvOld : col S u.val v.val = some b :=
      (inducedColour_some_iff S () _ u v bI).mp huv
    have hvzOld : col S v.val z.val = some b :=
      (inducedColour_some_iff S () _ v z bI).mp hvz
    have huzOld : col S u.val z.val = some d :=
      (inducedColour_some_iff S () _ u z dI).mp huz
    have hYuz := ParityHasse.Relative.odd_mul_subset Y.val U.val htwo u z
      ⟨v,hodd u v huvOld,hodd v z hvzOld⟩
    change col S u.val z.val ∈ plus S R.val at hYuz
    rwa [huzOld,some_mem_plus] at hYuz
  have hlocal := loc R P hP hfixP b hbP hsquare
  apply hbR
  change ∀ p ∈ Set.range q, prod S {some p} {some b} = {some p}
  rintro p ⟨a,rfl⟩
  exact hlocal (q a) (hpP a)

theorem fibre_class_of_palette_containment (H : HomogeneousSource S G)
    (hT : ∀ c : Atom S, (∀ a : ↥A, c ∈ square S (q a)) →
      c ∈ (fibreSpokeFixer S A q H).val)
    (x : FibreSet S A q) (y : M) :
    y ∈ FibreSet S A q ↔ supportEquiv S (fibreSpokeFixer S A q H) x.val y := by
  constructor
  · intro hy
    cases hc : col S x.val y with
    | none =>
      have he : x.val = y := (col_none S _ _).mp hc
      exact he ▸ (supportEquiv S _).val.refl x.val
    | some c =>
      have hcp : ∀ a : ↥A, c ∈ square S (q a) := fun a =>
        (mem_row S _ _ _).mpr ⟨x.val,a.val,y,x.property a,(col_symm S _ _).trans (hy a),hc⟩
      change col S x.val y ∈ plus S _
      rw [hc,some_mem_plus]
      exact hT c hcp
  · exact fibreSpokeFixer_closed S A q H x y

end CCO.RealHull.Geometry
