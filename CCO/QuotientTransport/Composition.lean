import CCO.QuotientTransport.Lattice

universe u v w z
namespace CCO.QuotientTransport
variable {G : Type u} [Group G]
variable {A : Type v} {B : Type w} {C : Type z}
variable [MulAction G A] [MulAction G B] [MulAction G C]

namespace InvEq
def quotientCongr {E F : InvEq G A} (h : E = F) : Quotient E.val ≃ Quotient F.val := by
  cases h
  exact Equiv.refl _
@[simp] theorem quotientCongr_mk {E F : InvEq G A} (h : E = F) (x : A) :
    quotientCongr h (Quotient.mk'' x) = Quotient.mk'' x := by cases h; rfl
end InvEq

namespace Transport
variable {E : InvEq G A} {R : Rel A B} {S : Rel B C}
variable (T : Transport E R) (U : Transport T.target S)

/-- C09: both actual kernel conditions, on the literal intermediate kernel. -/
theorem composite : Transport E (compose R S) where
  serial x := by
    obtain ⟨y,hy⟩ := T.serial x
    obtain ⟨z,hz⟩ := U.serial y
    exact ⟨z,y,hy,hz⟩
  coserial z := by
    obtain ⟨y,hy⟩ := U.coserial z
    obtain ⟨x,hx⟩ := T.coserial y
    exact ⟨x,y,hx,hy⟩
  invariant g x z := by
    rintro ⟨y,hy,hz⟩
    exact ⟨g • y,T.invariant g x y hy,U.invariant g y z hz⟩
  kernel x x' z := by
    rintro ⟨y,hxy,hyz⟩ ⟨y',hx'y',hy'z⟩
    obtain ⟨a,b,ha,hab,hb⟩ := (T.target_iff y y').mp (U.kernel y y' z hyz hy'z)
    exact E.val.trans (T.kernel x a y hxy ha)
      (E.val.trans hab (T.kernel b x' y' hb hx'y'))

/-- C10: literal equality of actual kernels, not an unrelated quotient chart. -/
theorem composite_target : (T.composite U).target = U.target := by
  apply InvEq.ext
  intro z z'
  rw [(T.composite U).target_iff,U.target_iff]
  constructor
  · rintro ⟨x,x',⟨y,hxy,hyz⟩,hxx',⟨y',hx'y',hy'z'⟩⟩
    exact ⟨y,y',hyz,(T.target_iff y y').mpr ⟨x,x',hxy,hxx',hx'y'⟩,hy'z'⟩
  · rintro ⟨y,y',hyz,hyy',hy'z'⟩
    obtain ⟨x,x',hxy,hxx',hx'y'⟩ := (T.target_iff y y').mp hyy'
    exact ⟨x,x',⟨y,hxy,hyz⟩,hxx',⟨y',hx'y',hy'z'⟩⟩

/-- C11: composition on the SAME displayed intermediate quotient. -/
theorem composite_quotient (q : Quotient E.val) :
    InvEq.quotientCongr (T.composite_target U) ((T.composite U).quotientEquiv q) =
      U.quotientEquiv (T.quotientEquiv q) := by
  induction q using Quotient.inductionOn with
  | _ x =>
    obtain ⟨y,hy⟩ := T.serial x
    obtain ⟨z,hz⟩ := U.serial y
    rw [(T.composite U).quotientEquiv_edge ⟨y,hy,hz⟩,InvEq.quotientCongr_mk,
      T.quotientEquiv_edge hy,U.quotientEquiv_edge hz]

theorem enlarge_label {H : InvEq G A} (h : E ≤ H) (y : B) :
    (T.enlarge h).label y = Quot.mapRight h (T.label y) := by
  rw [(T.enlarge h).label_edge (T.predecessor_spec y)]
  rfl
end Transport
end CCO.QuotientTransport
