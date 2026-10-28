import CCO.RealHull.Geometry.Globalisation

/-!
# C18: actual finite-fibre invariant intervals and chains

These are applications AFTER the genuine global-class existence theorem.
The domain is the original full interval below the canonical spoke fixer; the
codomain is the ACTUAL fibre, including its whole induced automorphism group.
Old-point quotient maps preserve actual relative classes and all chain indices.
-/

universe v w z t
namespace CCO.RealHull.Geometry
open ParityHasse.Original
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))

noncomputable def inducedSetColourIso {Z W : Set M} [Nonempty Z] [Nonempty W]
    (h : Z = W) :
    ColourEq (inducedSource S () Z) () ≃o ColourEq (inducedSource S () W) () := by
  cases h
  exact OrderIso.refl _

noncomputable def inducedSetFullIso {Z W : Set M} (h : Z = W) :
    InducedFullEq S () Z ≃o InducedFullEq S () W := by
  cases h
  exact OrderIso.refl _

def inducedOriginalRestrict (Z : Set M) [Nonempty Z] (F : ColourEq S ()) :
    ColourEq (inducedSource S () Z) () :=
  ⟨Setoid.comap (fun x : Z => x.val) F.val,by
    intro x y x' y' hc
    exact F.property _ _ _ _ ((inducedColour_eq_iff S () Z x y x' y').mp hc)⟩

theorem inducedSetColourIso_restrict {Z W : Set M} [Nonempty Z] [Nonempty W]
    (h : Z = W) (F : ColourEq S ()) :
    inducedSetColourIso S h (inducedOriginalRestrict S Z F) = inducedOriginalRestrict S W F := by
  cases h
  rfl

theorem inducedSetIso_val {Z W : Set M} [Nonempty Z] [Nonempty W] (h : Z = W)
    (F : InducedFullEq S () Z) (K : ColourEq (inducedSource S () Z) ()) (hk : F.val = K.val) :
    (inducedSetFullIso S h F).val = (inducedSetColourIso S h K).val := by
  cases h
  exact hk

variable [DecidableEq M] (A : Finset M) (q : ↥A → Atom S)
variable [Nonempty (FibreSet S A q)]
variable {G : Type t} [Group G] [MulAction G M]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,0,w} S)
variable [Finite (FibreSet S A q)] (x : FibreSet S A q)
include cco x

local instance fibreClassSetNonempty :
    Nonempty {y | supportEquiv S (fibreSpokeFixer S A q H) x.val y} :=
  ⟨⟨x.val,(supportEquiv S (fibreSpokeFixer S A q H)).val.refl x.val⟩⟩

theorem finite_fibre_set_eq_class :
    FibreSet S A q = {y | supportEquiv S (fibreSpokeFixer S A q H) x.val y} := by
  ext y
  exact finite_fibre_global_class S A q H cco x y

noncomputable def finiteFibreIntervalIso :
    Set.Iic (supportEquiv S (fibreSpokeFixer S A q H)) ≃o ColourEq (fibreSource S A q) () :=
  (classIntervalIso S () (supportEquiv S (fibreSpokeFixer S A q H)) x.val H).trans
    (inducedSetColourIso S (finite_fibre_set_eq_class S A q H cco x).symm)

noncomputable def finiteFibreFullIntervalIso :
    Set.Iic (supportEquiv S (fibreSpokeFixer S A q H)) ≃o
      InducedFullEq S () (FibreSet S A q) :=
  (classFullIntervalIso S () H (supportEquiv S (fibreSpokeFixer S A q H)) x.val).trans
    (inducedSetFullIso S (finite_fibre_set_eq_class S A q H cco x).symm)

theorem finiteFibreFullIntervalIso_val
    (F : Set.Iic (supportEquiv S (fibreSpokeFixer S A q H))) :
    (finiteFibreFullIntervalIso S A q H cco x F).val =
      (finiteFibreIntervalIso S A q H cco x F).val :=
  inducedSetIso_val S (finite_fibre_set_eq_class S A q H cco x).symm _ _ rfl

theorem finiteFibreIntervalIso_apply
    (F : Set.Iic (supportEquiv S (fibreSpokeFixer S A q H))) :
    finiteFibreIntervalIso S A q H cco x F = inducedOriginalRestrict S (FibreSet S A q) F.val :=
  inducedSetColourIso_restrict S (finite_fibre_set_eq_class S A q H cco x).symm F.val

theorem finiteFibreIntervalIso_readout
    (F : Set.Iic (supportEquiv S (fibreSpokeFixer S A q H))) (p r : FibreSet S A q) :
    finiteFibreIntervalIso S A q H cco x F p r ↔ F.val p.val r.val := by
  rw [finiteFibreIntervalIso_apply]
  rfl

theorem finiteFibreLift_closed
    (F : Set.Iic (supportEquiv S (fibreSpokeFixer S A q H)))
    (p : FibreSet S A q) (y : M) (hF : F.val p.val y) : y ∈ FibreSet S A q := by
  apply (finite_fibre_global_class S A q H cco x y).mpr
  exact (supportEquiv S _).val.trans
    ((finite_fibre_global_class S A q H cco x p.val).mp p.property) (F.property hF)

def finiteFibreRestrictedRelativeEquiv
    (F K : Set.Iic (supportEquiv S (fibreSpokeFixer S A q H))) (p : FibreSet S A q) :
    RelativeClass F.val.val K.val.val p.val ≃
      RelativeClass (inducedOriginalRestrict S (FibreSet S A q) F.val).val
        (inducedOriginalRestrict S (FibreSet S A q) K.val).val p where
  toFun := Quotient.map (fun y =>
    (⟨(⟨y.val,finiteFibreLift_closed S A q H cco x K p y.val y.property⟩ : FibreSet S A q),y.property⟩ :
      {y : FibreSet S A q // inducedOriginalRestrict S (FibreSet S A q) K.val p y}))
    (fun _ _ h => h)
  invFun := Quotient.map (fun y => (⟨y.val.val,y.property⟩ : {y // K.val p.val y}))
    (fun _ _ h => h)
  left_inv y := by induction y using Quotient.inductionOn with | _ y => rfl
  right_inv y := by induction y using Quotient.inductionOn with | _ y => rfl

noncomputable def finiteFibreRelativeEquiv
    (F K : Set.Iic (supportEquiv S (fibreSpokeFixer S A q H))) (p : FibreSet S A q) :
    RelativeClass F.val.val K.val.val p.val ≃
      RelativeClass (finiteFibreIntervalIso S A q H cco x F).val
        (finiteFibreIntervalIso S A q H cco x K).val p := by
  rw [finiteFibreIntervalIso_apply,finiteFibreIntervalIso_apply]
  exact finiteFibreRestrictedRelativeEquiv S A q H cco x F K p

theorem finite_fibre_relativeIndex
    (F K : Set.Iic (supportEquiv S (fibreSpokeFixer S A q H))) (p : FibreSet S A q) :
    relativeIndex F.val.val K.val.val p.val =
      relativeIndex (finiteFibreIntervalIso S A q H cco x F).val
        (finiteFibreIntervalIso S A q H cco x K).val p :=
  Nat.card_congr (finiteFibreRelativeEquiv S A q H cco x F K p)

theorem finite_fibre_full_relativeIndex
    (F K : Set.Iic (supportEquiv S (fibreSpokeFixer S A q H))) (p : FibreSet S A q) :
    relativeIndex F.val.val K.val.val p.val =
      relativeIndex (finiteFibreFullIntervalIso S A q H cco x F).val
        (finiteFibreFullIntervalIso S A q H cco x K).val p := by
  rw [finiteFibreFullIntervalIso_val,finiteFibreFullIntervalIso_val]
  exact finite_fibre_relativeIndex S A q H cco x F K p

theorem finite_fibre_family_lift_unique {J : Type z}
    (C : J → ColourEq (fibreSource S A q) ()) :
    ∃! F : J → Set.Iic (supportEquiv S (fibreSpokeFixer S A q H)),
      ∀ j, finiteFibreIntervalIso S A q H cco x (F j) = C j := by
  let e := finiteFibreIntervalIso S A q H cco x
  refine ⟨fun j => e.symm (C j),fun j => e.apply_symm_apply (C j),?_⟩
  intro F hF
  funext j
  exact e.injective ((hF j).trans (e.apply_symm_apply (C j)).symm)

theorem finite_fibre_full_family_lift_unique {J : Type z}
    (C : J → InducedFullEq S () (FibreSet S A q)) :
    ∃! F : J → Set.Iic (supportEquiv S (fibreSpokeFixer S A q H)),
      ∀ j, finiteFibreFullIntervalIso S A q H cco x (F j) = C j := by
  let e := finiteFibreFullIntervalIso S A q H cco x
  refine ⟨fun j => e.symm (C j),fun j => e.apply_symm_apply (C j),?_⟩
  intro F hF
  funext j
  exact e.injective ((hF j).trans (e.apply_symm_apply (C j)).symm)

theorem finite_fibre_full_chain_strict {n : Nat}
    (C : Fin (n+1) → InducedFullEq S () (FibreSet S A q)) (hC : StrictMono C) :
    StrictMono (fun j => (finiteFibreFullIntervalIso S A q H cco x).symm (C j)) :=
  (finiteFibreFullIntervalIso S A q H cco x).symm.strictMono.comp hC

noncomputable def finiteFibreLiftChain {n : Nat}
    (C : Fin (n+1) → ColourEq (fibreSource S A q) ()) :
    Fin (n+1) → Set.Iic (supportEquiv S (fibreSpokeFixer S A q H)) :=
  fun j => (finiteFibreIntervalIso S A q H cco x).symm (C j)

theorem finite_fibre_chain_strict {n : Nat}
    (C : Fin (n+1) → ColourEq (fibreSource S A q) ()) (hC : StrictMono C) :
    StrictMono (finiteFibreLiftChain S A q H cco x C) :=
  (finiteFibreIntervalIso S A q H cco x).symm.strictMono.comp hC

theorem finite_fibre_chain_indices {n : Nat}
    (C : Fin (n+1) → ColourEq (fibreSource S A q) ())
    (j k : Fin (n+1)) (p : FibreSet S A q) :
    relativeIndex (finiteFibreLiftChain S A q H cco x C j).val.val
      (finiteFibreLiftChain S A q H cco x C k).val.val p.val = relativeIndex (C j).val (C k).val p := by
  have hi := finite_fibre_relativeIndex S A q H cco x
    (finiteFibreLiftChain S A q H cco x C j) (finiteFibreLiftChain S A q H cco x C k) p
  have hj : finiteFibreIntervalIso S A q H cco x (finiteFibreLiftChain S A q H cco x C j) = C j :=
    (finiteFibreIntervalIso S A q H cco x).apply_symm_apply (C j)
  have hk : finiteFibreIntervalIso S A q H cco x (finiteFibreLiftChain S A q H cco x C k) = C k :=
    (finiteFibreIntervalIso S A q H cco x).apply_symm_apply (C k)
  rw [hj,hk] at hi
  exact hi

end CCO.RealHull.Geometry
