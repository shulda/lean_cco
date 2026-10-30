import CCO.QuotientTransport.Core
import Mathlib.Order.Hom.CompleteLattice

universe u v w
namespace CCO.QuotientTransport
variable {G : Type u} [Group G]
variable {A : Type v} {B : Type w} [MulAction G A] [MulAction G B]
namespace Transport
variable {E : InvEq G A} {R : Rel A B} (T : Transport E R)

def enlarge {H : InvEq G A} (h : E ≤ H) : Transport H R :=
  ⟨T.serial,T.coserial,T.invariant,fun _ _ _ ha hb => h (T.kernel _ _ _ ha hb)⟩

noncomputable def push (H : InvEq G A) (h : E ≤ H) : InvEq G B := (T.enlarge h).target
theorem push_iff (H : InvEq G A) (h : E ≤ H) (y z : B) :
    T.push H h y z ↔ ∃ x x', R x y ∧ H x x' ∧ R x' z := (T.enlarge h).target_iff y z
theorem target_le_push (H : InvEq G A) (h : E ≤ H) : T.target ≤ T.push H h := by
  intro y z hyz
  obtain ⟨x,x',hx,he,hx'⟩ := (T.target_iff y z).mp hyz
  exact (T.push_iff H h y z).mpr ⟨x,x',hx,h he,hx'⟩

noncomputable def reverse : Transport T.target (converse R) where
  serial := T.coserial
  coserial := T.serial
  invariant := fun g y x h => T.invariant g x y h
  kernel := fun y z x hy hz => (T.target_iff y z).mpr ⟨x,x,hy,E.val.refl x,hz⟩

noncomputable def pull (L : InvEq G B) (h : T.target ≤ L) : InvEq G A := (T.reverse.enlarge h).target
theorem pull_iff (L : InvEq G B) (h : T.target ≤ L) (x z : A) :
    T.pull L h x z ↔ ∃ y y', R x y ∧ L y y' ∧ R z y' := (T.reverse.enlarge h).target_iff x z
theorem source_le_pull (L : InvEq G B) (h : T.target ≤ L) : E ≤ T.pull L h := by
  intro x z hxz
  obtain ⟨y,hy⟩ := T.serial x
  obtain ⟨y',hy'⟩ := T.serial z
  exact (T.pull_iff L h x z).mpr ⟨y,y',hy,h ((T.target_iff y y').mpr ⟨x,z,hy,hxz,hy'⟩),hy'⟩

theorem pull_push (H : InvEq G A) (h : E ≤ H) :
    T.pull (T.push H h) (T.target_le_push H h) = H := by
  apply InvEq.ext
  intro x z
  constructor
  · intro hrel
    obtain ⟨y,y',hy,hyy',hy'⟩ := (T.pull_iff _ _ x z).mp hrel
    obtain ⟨a,b,ha,hab,hb⟩ := (T.push_iff H h y y').mp hyy'
    exact H.val.trans (h (T.kernel x a y hy ha))
      (H.val.trans hab (h (T.kernel b z y' hb hy')))
  · intro hxz
    obtain ⟨y,hy⟩ := T.serial x
    obtain ⟨y',hy'⟩ := T.serial z
    exact (T.pull_iff _ _ x z).mpr ⟨y,y',hy,(T.push_iff H h y y').mpr ⟨x,z,hy,hxz,hy'⟩,hy'⟩

theorem push_pull (L : InvEq G B) (h : T.target ≤ L) :
    T.push (T.pull L h) (T.source_le_pull L h) = L := by
  apply InvEq.ext
  intro y z
  constructor
  · intro hrel
    obtain ⟨x,x',hx,hxx',hx'⟩ := (T.push_iff _ _ y z).mp hrel
    obtain ⟨a,b,ha,hab,hb⟩ := (T.pull_iff L h x x').mp hxx'
    exact L.val.trans (h ((T.target_iff y a).mpr ⟨x,x,hx,E.val.refl x,ha⟩))
      (L.val.trans hab (h ((T.target_iff b z).mpr ⟨x',x',hb,E.val.refl x',hx'⟩)))
  · intro hyz
    obtain ⟨x,hx⟩ := T.coserial y
    obtain ⟨x',hx'⟩ := T.coserial z
    exact (T.push_iff _ _ y z).mpr ⟨x,x',hx,(T.pull_iff L h x x').mpr ⟨y,z,hx,hyz,hx'⟩,hx'⟩

/-- C07/QT2: ALL invariant equivalences, with literal relational inverse. -/
noncomputable def intervalIso : {H : InvEq G A // E ≤ H} ≃o
    {L : InvEq G B // T.target ≤ L} where
  toFun H := ⟨T.push H.val H.property,T.target_le_push H.val H.property⟩
  invFun L := ⟨T.pull L.val L.property,T.source_le_pull L.val L.property⟩
  left_inv H := Subtype.ext (T.pull_push H.val H.property)
  right_inv L := Subtype.ext (T.push_pull L.val L.property)
  map_rel_iff' := by
    intro H K
    constructor
    · intro h x z hxz
      obtain ⟨y,hy⟩ := T.serial x
      obtain ⟨y',hy'⟩ := T.serial z
      have hp := h ((T.push_iff H.val H.property y y').mpr ⟨x,z,hy,hxz,hy'⟩)
      obtain ⟨a,b,ha,hab,hb⟩ := (T.push_iff K.val K.property y y').mp hp
      exact K.val.val.trans (K.property (T.kernel x a y hy ha))
        (K.val.val.trans hab (K.property (T.kernel b z y' hb hy')))
    · intro h y z hyz
      obtain ⟨x,x',hx,he,hx'⟩ := (T.push_iff H.val H.property y z).mp hyz
      exact (T.push_iff K.val K.property y z).mpr ⟨x,x',hx,h he,hx'⟩

/-- C06: the ordinary setoid quotient correspondence, restricted to exactly
the invariant relations under the actual quotient action. -/
def descend (H : InvEq G A) (h : E ≤ H) : Setoid (Quotient E.val) :=
  Setoid.correspondence E.val ⟨H.val,h⟩
@[simp] theorem descend_mk (H : InvEq G A) (h : E ≤ H) (x y : A) :
    descend H h (Quotient.mk'' x) (Quotient.mk'' y) ↔ H x y := Iff.rfl
theorem descend_invariant (H : InvEq G A) (h : E ≤ H) (g : G)
    (q q' : Quotient E.val) (hq : descend H h q q') :
    descend H h (E.act g q) (E.act g q') := by
  induction q using Quotient.inductionOn with
  | _ x =>
    induction q' using Quotient.inductionOn with
    | _ y => exact H.property g x y hq

/-- Covers, without any distributivity or finite-lattice assumption. -/
def Covers {L : Type*} [PartialOrder L] (x y : L) : Prop :=
  x < y ∧ ∀ z, x ≤ z → z ≤ y → z = x ∨ z = y
theorem intervalIso_covers (H K : {H : InvEq G A // E ≤ H}) :
    Covers (T.intervalIso H) (T.intervalIso K) ↔ Covers H K := by
  constructor
  · rintro ⟨hlt,hgap⟩
    refine ⟨(T.intervalIso.lt_iff_lt).mp hlt,fun z hx hy => ?_⟩
    rcases hgap (T.intervalIso z) (T.intervalIso.monotone hx) (T.intervalIso.monotone hy) with hz | hz
    · exact Or.inl (T.intervalIso.injective hz)
    · exact Or.inr (T.intervalIso.injective hz)
  · rintro ⟨hlt,hgap⟩
    refine ⟨(T.intervalIso.lt_iff_lt).mpr hlt,fun z hx hy => ?_⟩
    rcases hgap (T.intervalIso.symm z) (by simpa using T.intervalIso.symm.monotone hx)
        (by simpa using T.intervalIso.symm.monotone hy) with hz | hz
    · exact Or.inl (by simpa using congrArg T.intervalIso hz)
    · exact Or.inr (by simpa using congrArg T.intervalIso hz)

theorem push_inf (H K : InvEq G A) (hH : E ≤ H) (hK : E ≤ K) :
    T.push (H ⊓ K) (le_inf hH hK) = T.push H hH ⊓ T.push K hK := by
  apply InvEq.ext
  intro y z
  constructor
  · rintro h
    obtain ⟨x,x',hx,he,hx'⟩ := (T.push_iff _ _ y z).mp h
    exact (InvEq.inf_apply _ _ y z).mpr ⟨(T.push_iff _ _ y z).mpr ⟨x,x',hx,((InvEq.inf_apply H K x x').mp he).1,hx'⟩,
      (T.push_iff _ _ y z).mpr ⟨x,x',hx,((InvEq.inf_apply H K x x').mp he).2,hx'⟩⟩
  · intro h
    obtain ⟨hH',hK'⟩ := (InvEq.inf_apply _ _ y z).mp h
    obtain ⟨x,x',hx,hxx',hx'⟩ := (T.push_iff _ _ y z).mp hH'
    obtain ⟨a,b,ha,hab,hb⟩ := (T.push_iff _ _ y z).mp hK'
    exact (T.push_iff _ _ y z).mpr ⟨x,x',hx,(InvEq.inf_apply H K x x').mpr ⟨hxx',K.val.trans (hK (T.kernel x a y hx ha))
      (K.val.trans hab (hK (T.kernel b x' z hb hx')))⟩,hx'⟩

/-- All existing suprema/infima in either upper interval are carried to
the corresponding bounds. This also covers arbitrary (including empty)
families; joins are not postulated to be relational composition. -/
theorem intervalIso_isLUB (s : Set {H : InvEq G A // E ≤ H}) (H : {H : InvEq G A // E ≤ H}) :
    IsLUB (T.intervalIso '' s) (T.intervalIso H) ↔ IsLUB s H := by
  constructor
  · rintro ⟨hub,hle⟩
    refine ⟨fun x hx => (T.intervalIso.le_iff_le).mp (hub ⟨x,hx,rfl⟩),fun x hx => ?_⟩
    apply (T.intervalIso.le_iff_le).mp
    apply hle
    rintro _ ⟨z,hz,rfl⟩
    exact T.intervalIso.monotone (hx hz)
  · rintro ⟨hub,hle⟩
    refine ⟨?_,fun x hx => ?_⟩
    · rintro _ ⟨z,hz,rfl⟩
      exact T.intervalIso.monotone (hub hz)
    · have hh : H ≤ T.intervalIso.symm x := hle (fun z hz => by
        apply (T.intervalIso.le_iff_le).mp
        simpa using hx ⟨z,hz,rfl⟩)
      simpa using T.intervalIso.monotone hh

theorem intervalIso_isGLB (s : Set {H : InvEq G A // E ≤ H}) (H : {H : InvEq G A // E ≤ H}) :
    IsGLB (T.intervalIso '' s) (T.intervalIso H) ↔ IsGLB s H := by
  constructor
  · rintro ⟨hlb,hle⟩
    refine ⟨fun x hx => (T.intervalIso.le_iff_le).mp (hlb ⟨x,hx,rfl⟩),fun x hx => ?_⟩
    apply (T.intervalIso.le_iff_le).mp
    apply hle
    rintro _ ⟨z,hz,rfl⟩
    exact T.intervalIso.monotone (hx hz)
  · rintro ⟨hlb,hle⟩
    refine ⟨?_,fun x hx => ?_⟩
    · rintro _ ⟨z,hz,rfl⟩
      exact T.intervalIso.monotone (hlb hz)
    · have hh : T.intervalIso.symm x ≤ H := hle (fun z hz => by
        apply (T.intervalIso.le_iff_le).mp
        simpa using hx ⟨z,hz,rfl⟩)
      simpa using T.intervalIso.monotone hh
end Transport
end CCO.QuotientTransport
