import CCO.FiniteFibres.Group.Correspondence.Basic
import Mathlib.Order.Cover
import Mathlib.GroupTheory.Index

/-! C23–C24: actual relative quotient classes and subgroup indices. The
class object is the literal fibre of Quotient U → Quotient V; the coset
bijection and its uniformity do not assume a finite or faithful acting group. -/

universe u v
namespace CCO.FiniteFibres.Group.Correspondence

variable {G : Type u} [Group G] {A : Type v} [MulAction G A]

def RelativeClass (U V : InvEq G A) (h : U ≤ V) (a : A) :=
  {q : Quotient U.val // Quotient.map id (fun {_ _} hxy => h hxy) q = Quotient.mk V.val a}

namespace InvEq

@[instance_reducible] def quotientAction (E : InvEq G A) : MulAction G (Quotient E.val) where
  smul g q := Quotient.map (g • ·) (fun {_ _} h => E.property g _ _ h) q
  one_smul q := Quotient.inductionOn q fun x => congrArg (Quotient.mk E.val) (one_smul G x)
  mul_smul g h q := Quotient.inductionOn q fun x => congrArg (Quotient.mk E.val) (mul_smul g h x)

def act (E : InvEq G A) (g : G) (q : Quotient E.val) : Quotient E.val :=
  @SMul.smul G (Quotient E.val) E.quotientAction.toSMul g q

@[simp] theorem act_mk (E : InvEq G A) (g : G) (x : A) :
    E.act g (Quotient.mk E.val x) = Quotient.mk E.val (g • x) := rfl

end InvEq

def relativeMove {U V : InvEq G A} (h : U ≤ V) {a b : A} (g : G) (hg : g • a = b) :
    RelativeClass U V h a ≃ RelativeClass U V h b where
  toFun q := ⟨U.act g q.val,by
    rcases q with ⟨q,hq⟩
    induction q using Quotient.inductionOn with
    | _ x =>
      apply Quotient.sound
      have hx : V x a := Quotient.exact hq
      exact hg ▸ V.property g x a hx⟩
  invFun q := ⟨U.act g⁻¹ q.val,by
    rcases q with ⟨q,hq⟩
    induction q using Quotient.inductionOn with
    | _ x =>
      apply Quotient.sound
      have hx : V x b := Quotient.exact hq
      have hga : g⁻¹ • b = a := by rw [← hg,inv_smul_smul]
      exact hga ▸ V.property g⁻¹ x b hx⟩
  left_inv q := by
    apply Subtype.ext
    rcases q with ⟨q,hq⟩
    induction q using Quotient.inductionOn with
    | _ x => exact congrArg (Quotient.mk U.val) (inv_smul_smul g x)
  right_inv q := by
    apply Subtype.ext
    rcases q with ⟨q,hq⟩
    induction q using Quotient.inductionOn with
    | _ x => exact congrArg (Quotient.mk U.val) (smul_inv_smul g x)

variable (trans : ∀ x y : A, ∃ g : G, g • x = y) (a : A)

noncomputable def cosetToRelative (U V : InvEq G A) (h : U ≤ V) :
    (V.subgroup a ⧸ (U.subgroup a).subgroupOf (V.subgroup a)) → RelativeClass U V h a :=
  Quotient.lift (fun g : V.subgroup a => ⟨Quotient.mk U.val (g.val • a),Quotient.sound g.property⟩)
    (fun g k hgk => by
      have h0 : g⁻¹*k ∈ (U.subgroup a).subgroupOf (V.subgroup a) :=
        (QuotientGroup.leftRel_apply (s := (U.subgroup a).subgroupOf (V.subgroup a))).mp hgk
      exact Subtype.ext (Quotient.sound ((U.relative_motion_iff a g.val k.val).mp h0)))

include trans in
theorem cosetToRelative_bijective (U V : InvEq G A) (h : U ≤ V) :
    Function.Bijective (cosetToRelative a U V h) := by
  constructor
  · intro q r hqr
    induction q using Quotient.inductionOn with
    | _ g =>
      induction r using Quotient.inductionOn with
      | _ k =>
        have heq : Quotient.mk U.val (g.val • a) = Quotient.mk U.val (k.val • a) :=
          congrArg Subtype.val hqr
        apply Quotient.sound
        apply (QuotientGroup.leftRel_apply).mpr
        exact (U.relative_motion_iff a g.val k.val).mpr (Quotient.exact heq)
  · rintro ⟨q,hq⟩
    induction q using Quotient.inductionOn with
    | _ x =>
      have hx : V x a := Quotient.exact hq
      obtain ⟨g,hg⟩ := trans a x
      let gV : V.subgroup a := ⟨g,by change V (g • a) a; exact hg.symm ▸ hx⟩
      refine ⟨Quotient.mk _ gV,Subtype.ext ?_⟩
      change Quotient.mk U.val (g • a) = Quotient.mk U.val x
      exact congrArg (Quotient.mk U.val) hg

/-- C23: the actual cosets inside H_V are in bijection with the literal
fibre of the quotient map U→V over the original class of a. -/
noncomputable def cosetEquivRelative (U V : InvEq G A) (h : U ≤ V) :
    (V.subgroup a ⧸ (U.subgroup a).subgroupOf (V.subgroup a)) ≃ RelativeClass U V h a :=
  Equiv.ofBijective (cosetToRelative a U V h) (cosetToRelative_bijective trans a U V h)

include trans in
theorem relative_card_eq_index (U V : InvEq G A) (h : U ≤ V) :
    Nat.card (RelativeClass U V h a) = ((U.subgroup a).subgroupOf (V.subgroup a)).index :=
  (Nat.card_congr (cosetEquivRelative trans a U V h).symm).trans
    ((U.subgroup a).subgroupOf (V.subgroup a)).index_eq_card.symm

include trans in
theorem relative_card_uniform (U V : InvEq G A) (h : U ≤ V) (a b : A) :
    Nat.card (RelativeClass U V h a) = Nat.card (RelativeClass U V h b) := by
  obtain ⟨g,hg⟩ := trans a b
  exact Nat.card_congr (relativeMove h g hg)

include trans in
theorem subgroup_cover {U V : InvEq G A} (h : U ⋖ V) :
    U.subgroup a < V.subgroup a ∧
    ∀ W : Subgroup G, U.subgroup a ≤ W → W ≤ V.subgroup a →
      W = U.subgroup a ∨ W = V.subgroup a := by
  have hUV := (subgroup_le_iff trans a U V).mpr h.le
  refine ⟨lt_of_le_of_ne hUV (fun heq => h.ne ((subgroupCorrespondence trans a).injective (Subtype.ext heq))),?_⟩
  intro W hUW hWV
  let hstab := (U.stabilizer_le a).trans hUW
  let E := ofSubgroup trans a W hstab
  have hE : E.subgroup a = W := subgroup_ofSubgroup trans a W hstab
  have hUE : U ≤ E := (subgroup_le_iff trans a U E).mp (by rw [hE]; exact hUW)
  have hEV : E ≤ V := (subgroup_le_iff trans a E V).mp (by rw [hE]; exact hWV)
  rcases h.eq_or_eq hUE hEV with hEq | hEq
  · exact Or.inl (hE.symm.trans (congrArg (fun E : InvEq G A => E.subgroup a) hEq))
  · exact Or.inr (hE.symm.trans (congrArg (fun E : InvEq G A => E.subgroup a) hEq))

include trans in
/-- C24 in the exact ordinary-subgroup form consumed by the local p-group
maximal-index theorem. No finite-group hypothesis occurs here. -/
theorem relative_subgroup_maximal {U V : InvEq G A} (h : U ⋖ V) :
    (U.subgroup a).subgroupOf (V.subgroup a) ≠ ⊤ ∧
    ∀ J : Subgroup (V.subgroup a),
      (U.subgroup a).subgroupOf (V.subgroup a) < J → J = ⊤ := by
  obtain ⟨hUV,hInterval⟩ := subgroup_cover trans a h
  constructor
  · intro htop
    exact hUV.not_ge (Subgroup.subgroupOf_eq_top.mp htop)
  · intro J hJ
    let W := J.map (V.subgroup a).subtype
    have hUW : U.subgroup a ≤ W := by
      intro g hg
      let gV : V.subgroup a := ⟨g,hUV.le hg⟩
      exact ⟨gV,hJ.le hg,rfl⟩
    have hWV : W ≤ V.subgroup a := by
      rintro x ⟨g,hg,rfl⟩
      exact g.property
    rcases hInterval W hUW hWV with hEq | hEq
    · exfalso
      apply hJ.not_ge
      intro g hg
      change g.val ∈ U.subgroup a
      have hw : g.val ∈ W := ⟨g,hg,rfl⟩
      rw [hEq] at hw
      exact hw
    · apply top_unique
      intro g _
      have hw : g.val ∈ W := hEq.symm ▸ g.property
      obtain ⟨k,hk,hkg⟩ := hw
      have heq : k = g := Subtype.ext hkg
      exact heq ▸ hk

end CCO.FiniteFibres.Group.Correspondence
