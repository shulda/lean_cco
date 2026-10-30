import CCO.FullPhaseLift.Canonical.UnaryExpansion
import CCO.FullPhaseLift.BinarySource.FullAlignment
import CCO.ParityHasse.Original.Equivalences

/-! Canonical actual two-point names are precisely the orbits of genuine
FULL old-language automorphisms. Only the complete induced one/two-point
structure is used; no higher tuple homogeneity is inferred from pair names. -/

universe v
namespace CCO.FullPhaseLift.Canonical
open ParityHasse.Original
attribute [local instance] Classical.propDecidable

private theorem code_equality {L : Signature} {M : Type v} (U : BoolTable L M)
    {x y z t : M} (h : pairNameCode U x y = pairNameCode U z t) : x = y ↔ z = t := by
  have hh := congrArg (fun c => c.2.2 = none) h
  simpa only [pairNameCode,ite_eq_left_iff,Option.some_ne_none,imp_false,not_not] using hh.to_iff

private theorem code_profile {L : Signature} {M : Type v} (U : BoolTable L M)
    {x y z t : M} (h : pairNameCode U x y = pairNameCode U z t) :
    pairProfile U x y = pairProfile U z t := by
  have hu := congrArg Prod.fst h
  have hp := congrArg (fun c => c.2.2) h
  by_cases hxy : x = y
  · have hzt := (code_equality U h).mp hxy
    subst y
    subst t
    simpa only [pairNameCode,pairProfile_self] using congrArg diagonalProfile hu
  · have hzt : z ≠ t := fun he => hxy ((code_equality U h).mpr he)
    simpa only [pairNameCode,if_neg hxy,if_neg hzt,Option.some.injEq] using hp

theorem full_pairNameCode {L : Signature} {M : Type v} {U : BoolTable L M}
    (a : Iso U U) (x y : M) :
    pairNameCode U (a.point x) (a.point y) = pairNameCode U x y := by
  have hx : unaryProfile U (a.point x) = unaryProfile U x := unaryProfile_embedding a.toEmbedding x
  have hy : unaryProfile U (a.point y) = unaryProfile U y := unaryProfile_embedding a.toEmbedding y
  have hp : pairProfile U (a.point x) (a.point y) = pairProfile U x y := pairProfile_embedding a.toEmbedding x y
  simp only [pairNameCode,hx,hy,hp,a.point.injective.eq_iff]

theorem pairNameCode_eq_iff_full_orbit {L : Signature} {M : Type v}
    (U : BoolTable L M) (hom : (toRelational U).Homogeneous) (x y z t : M) :
    pairNameCode U x y = pairNameCode U z t ↔
      ∃ a : Iso U U, a.point x = z ∧ a.point y = t := by
  constructor
  · intro h
    have he : ∀ i j : Fin 2, ![x,y] i = ![x,y] j ↔ ![z,t] i = ![z,t] j := by
      intro i j
      have hd := code_equality U h
      fin_cases i <;> fin_cases j
      · exact ⟨fun _ => rfl,fun _ => rfl⟩
      · exact hd
      · exact (eq_comm : y = x ↔ x = y).trans (hd.trans (eq_comm : z = t ↔ t = z))
      · exact ⟨fun _ => rfl,fun _ => rfl⟩
    have hp := code_profile U h
    have hr : ∀ {n} (R : L.language.Rel n) (xs : Fin n → Fin 2),
        (toRelational U).rel R (![x,y] ∘ xs) ↔ (toRelational U).rel R (![z,t] ∘ xs) := by
      intro n R xs
      have hh := congrFun hp ⟨R.val,xs ∘ Fin.cast R.property⟩
      exact (congrArg (fun b => b = true) hh).to_iff
    obtain ⟨a,ha⟩ := BinarySource.full_tuple_homogeneous (toRelational U) hom ![x,y] ![z,t] he hr
    exact ⟨a,ha 0,ha 1⟩
  · rintro ⟨a,hx,hy⟩
    simpa only [hx,hy] using (full_pairNameCode a x y).symm

def fullMove {L : Signature} {M : Type v} {U : BoolTable L M}
    (a : Iso U U) {i : UnaryName U} (x : Carrier U i) : Carrier U i :=
  ⟨a.point x.val,(unaryProfile_embedding a.toEmbedding x.val).trans x.property⟩

@[simp] theorem pack_carrier {L : Signature} {M : Type v} (U : BoolTable L M)
    {i : UnaryName U} (x : Carrier U i) : pack U x.val = ⟨i,x⟩ :=
  (pack U).apply_symm_apply ⟨i,x⟩

theorem colour_fullMove {L : Signature} {M : Type v} (U : BoolTable L M)
    (hsym : SameSortSymmetric U) (a : Iso U U) {i j : UnaryName U}
    (x : Carrier U i) (y : Carrier U j) :
    (source U hsym).colour (fullMove a x) (fullMove a y) = (source U hsym).colour x y := by
  have hc : taggedColour (source U hsym) (⟨i,fullMove a x⟩ : Sigma (Carrier U)) ⟨j,fullMove a y⟩ =
      taggedColour (source U hsym) ⟨i,x⟩ ⟨j,y⟩ := by
    apply tagCode_injective U
    rw [← pack_carrier U (fullMove a x),← pack_carrier U (fullMove a y),
      ← pack_carrier U x,← pack_carrier U y,tagCode_pack_eq_pairNameCode,tagCode_pack_eq_pairNameCode]
    exact full_pairNameCode a x.val y.val
  simpa only [taggedColour,Sigma.mk.injEq,heq_eq_eq,true_and] using hc

theorem colour_eq_iff_full_orbit {L : Signature} {M : Type v} (U : BoolTable L M)
    (hom : (toRelational U).Homogeneous) (hsym : SameSortSymmetric U)
    {i j : UnaryName U} (x x' : Carrier U i) (y y' : Carrier U j) :
    (source U hsym).colour x y = (source U hsym).colour x' y' ↔
      ∃ a : Iso U U, fullMove a x = x' ∧ fullMove a y = y' := by
  constructor
  · intro h
    have ht := congrArg (fun c => (⟨i,j,c⟩ : Σ i,Σ j,Option ((source U hsym).Atom i j))) h
    have hc := congrArg (tagCode U) ht
    change tagCode U (taggedColour (source U hsym) ⟨i,x⟩ ⟨j,y⟩) =
      tagCode U (taggedColour (source U hsym) ⟨i,x'⟩ ⟨j,y'⟩) at hc
    rw [← pack_carrier U x,← pack_carrier U y,← pack_carrier U x',← pack_carrier U y',
      tagCode_pack_eq_pairNameCode,tagCode_pack_eq_pairNameCode] at hc
    obtain ⟨a,hax,hay⟩ := (pairNameCode_eq_iff_full_orbit U hom _ _ _ _).mp hc
    exact ⟨a,Subtype.ext hax,Subtype.ext hay⟩
  · rintro ⟨a,hx,hy⟩
    rw [← hx,← hy,colour_fullMove]

abbrev FullInvariantEq {L : Signature} {M : Type v} (U : BoolTable L M) (i : UnaryName U) :=
  {E : Setoid (Carrier U i) // ∀ (a : Iso U U) x y, E x y → E (fullMove a x) (fullMove a y)}

theorem fullIsoInvariant_iff_colourInvariant {L : Signature} {M : Type v}
    (U : BoolTable L M) (hom : (toRelational U).Homogeneous) (hsym : SameSortSymmetric U)
    (i : UnaryName U) (R : Carrier U i → Carrier U i → Prop) :
    (∀ (a : Iso U U) x y, R x y → R (fullMove a x) (fullMove a y)) ↔
      ColourInvariant (source U hsym) i R := by
  constructor
  · intro hR x y x' y' hc
    constructor
    · intro h
      obtain ⟨a,hx,hy⟩ := (colour_eq_iff_full_orbit U hom hsym x x' y y').mp hc
      simpa only [hx,hy] using hR a x y h
    · intro h
      obtain ⟨a,hx,hy⟩ := (colour_eq_iff_full_orbit U hom hsym x' x y' y).mp hc.symm
      simpa only [hx,hy] using hR a x' y' h
  · intro hR a x y h
    exact (hR (fullMove a x) (fullMove a y) x y (colour_fullMove U hsym a x y)).mpr h

def fullInvariantOrderIso {L : Signature} {M : Type v}
    (U : BoolTable L M) (hom : (toRelational U).Homogeneous) (hsym : SameSortSymmetric U)
    (i : UnaryName U) : FullInvariantEq U i ≃o ColourEq (source U hsym) i where
  toFun E := ⟨E.val,(fullIsoInvariant_iff_colourInvariant U hom hsym i E.val).mp E.property⟩
  invFun E := ⟨E.val,(fullIsoInvariant_iff_colourInvariant U hom hsym i E.val).mpr E.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

def fullInvariant_relativeClassEquiv {L : Signature} {M : Type v}
    (U : BoolTable L M) (hom : (toRelational U).Homogeneous) (hsym : SameSortSymmetric U)
    (i : UnaryName U) (E F : FullInvariantEq U i) (a : Carrier U i) :
    RelativeClass E.val F.val a ≃
      RelativeClass (fullInvariantOrderIso U hom hsym i E).val
        (fullInvariantOrderIso U hom hsym i F).val a := Equiv.refl _

theorem fullInvariant_relativeIndex {L : Signature} {M : Type v}
    (U : BoolTable L M) (hom : (toRelational U).Homogeneous) (hsym : SameSortSymmetric U)
    (i : UnaryName U) (E F : FullInvariantEq U i) (a : Carrier U i) :
    relativeIndex E.val F.val a =
      relativeIndex (fullInvariantOrderIso U hom hsym i E).val
        (fullInvariantOrderIso U hom hsym i F).val a := rfl

end CCO.FullPhaseLift.Canonical
