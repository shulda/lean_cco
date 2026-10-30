import CCO.TypedRelation
import Mathlib.Data.Setoid.Basic
import Mathlib.Order.CompleteLattice.Defs

/-! Elementary invariant quotient transport. Relations are actual typed
equality-inclusive predicates; no CCO, exactness or definability is assumed. -/
universe u v w
namespace CCO.QuotientTransport

abbrev Rel (A : Type v) (B : Type w) := A → B → Prop
def compose {A B C : Type*} (R : Rel A B) (S : Rel B C) : Rel A C :=
  fun x z => ∃ y, R x y ∧ S y z
def converse {A B : Type*} (R : Rel A B) : Rel B A := fun y x => R x y
def Serial {A B : Type*} (R : Rel A B) : Prop := ∀ x, ∃ y, R x y
def Coserial {A B : Type*} (R : Rel A B) : Prop := ∀ y, ∃ x, R x y

variable {G : Type u} [Group G]
variable {A : Type v} {B : Type w} [MulAction G A] [MulAction G B]

def Invariant (R : Rel A B) : Prop := ∀ g : G, ∀ x y, R x y → R (g • x) (g • y)
abbrev InvEq (G : Type u) [Group G] (A : Type v) [MulAction G A] :=
  {E : Setoid A // Invariant (G := G) E.r}

namespace InvEq
instance : CoeFun (InvEq G A) (fun _ => A → A → Prop) := ⟨fun E => E.val.r⟩
instance : PartialOrder (InvEq G A) := inferInstanceAs (PartialOrder {E : Setoid A // _})
@[ext] theorem ext {E F : InvEq G A} (h : ∀ x y, E x y ↔ F x y) : E = F :=
  Subtype.ext (Setoid.ext h)

def meet (s : Set (InvEq G A)) : InvEq G A :=
  ⟨{ r := fun x y => ∀ E ∈ s, E x y
     iseqv := ⟨fun x E _ => E.val.refl x,
       fun h E hE => E.val.symm (h E hE),
       fun h h' E hE => E.val.trans (h E hE) (h' E hE)⟩ },
   fun g x y h E hE => E.property g x y (h E hE)⟩
instance : InfSet (InvEq G A) := ⟨meet⟩
instance : CompleteLattice (InvEq G A) := completeLatticeOfInf (InvEq G A) fun s =>
  ⟨fun E hE _ _ h => h E hE,fun _ h _ _ hxy E hE => h hE hxy⟩

@[simp] theorem sInf_apply (s : Set (InvEq G A)) (x y : A) :
    sInf s x y ↔ ∀ E ∈ s, E x y := Iff.rfl
@[simp] theorem top_apply (x y : A) : (⊤ : InvEq G A) x y ↔ True := by
  change (∀ E ∈ (∅ : Set (InvEq G A)), E x y) ↔ True
  simp
@[simp] theorem inf_apply (E F : InvEq G A) (x y : A) :
    (E ⊓ F) x y ↔ E x y ∧ F x y := by
  change (∀ K ∈ ({E,F} : Set (InvEq G A)), K x y) ↔ _
  simp

/-- The actual quotient action, as explicit data to avoid installing a
second global instance for the shared B001 quotient action. -/
@[instance_reducible] def quotientAction (E : InvEq G A) : MulAction G (Quotient E.val) where
  smul g q := Quotient.map (g • ·) (fun {x y} h => E.property g x y h) q
  one_smul q := Quotient.inductionOn q fun x => congrArg Quotient.mk'' (one_smul G x)
  mul_smul g h q := Quotient.inductionOn q fun x => congrArg Quotient.mk'' (mul_smul g h x)

def act (E : InvEq G A) (g : G) (q : Quotient E.val) : Quotient E.val :=
  @SMul.smul G (Quotient E.val) (E.quotientAction.toSMul) g q
@[simp] theorem act_mk (E : InvEq G A) (g : G) (x : A) :
    E.act g (Quotient.mk'' x) = Quotient.mk'' (g • x) := rfl
end InvEq

/-- C01: one actual witness and endpoint transitivity supply both sides. -/
theorem serial_coserial_of_invariant (R : Rel A B)
    (hR : Invariant (G := G) R) (hne : ∃ x y, R x y)
    (hA : ∀ x y : A, ∃ g : G, g • x = y)
    (hB : ∀ x y : B, ∃ g : G, g • x = y) : Serial R ∧ Coserial R := by
  obtain ⟨a,b,hab⟩ := hne
  constructor
  · intro x
    obtain ⟨g,rfl⟩ := hA a x
    exact ⟨g • b,hR g a b hab⟩
  · intro y
    obtain ⟨g,rfl⟩ := hB b y
    exact ⟨g • a,hR g a b hab⟩

/-- Only the local kernel premise is stored. It is derived afresh for
closed-word prefixes, rather than inherited as an unrelated hypothesis. -/
structure Transport (E : InvEq G A) (R : Rel A B) : Prop where
  serial : Serial R
  coserial : Coserial R
  invariant : Invariant (G := G) R
  kernel : ∀ x x' y, R x y → R x' y → E x x'

namespace Transport
variable {E : InvEq G A} {R : Rel A B} (T : Transport E R)

noncomputable def predecessor (y : B) : A := Classical.choose (T.coserial y)
theorem predecessor_spec (y : B) : R (T.predecessor y) y := Classical.choose_spec (T.coserial y)
noncomputable def label (y : B) : Quotient E.val := Quotient.mk'' (T.predecessor y)

/-- C02, the choice-free specification of the canonical label. -/
theorem label_edge {x : A} {y : B} (h : R x y) :
    T.label y = Quotient.mk'' x :=
  Quotient.sound (T.kernel _ _ y (T.predecessor_spec y) h)

theorem label_surjective : Function.Surjective T.label := by
  intro q
  induction q using Quotient.inductionOn with
  | _ x =>
    obtain ⟨y,hy⟩ := T.serial x
    exact ⟨y,T.label_edge hy⟩

theorem label_equivariant (g : G) (y : B) : T.label (g • y) = E.act g (T.label y) := by
  rw [T.label_edge (T.invariant g _ _ (T.predecessor_spec y))]
  rfl

noncomputable def target : InvEq G B :=
  ⟨Setoid.ker T.label,fun g x y h => by
    change T.label (g • x) = T.label (g • y)
    rw [T.label_equivariant,T.label_equivariant,h]⟩

/-- C04/QT1: equality of labels is exactly the literal existential relation. -/
theorem target_iff (y z : B) : T.target y z ↔ ∃ x x', R x y ∧ E x x' ∧ R x' z := by
  constructor
  · intro h
    exact ⟨T.predecessor y,T.predecessor z,T.predecessor_spec y,
      Quotient.exact h,T.predecessor_spec z⟩
  · rintro ⟨x,x',hx,he,hx'⟩
    change T.label y = T.label z
    rw [T.label_edge hx,T.label_edge hx']
    exact Quotient.sound he

noncomputable def labelEquiv : Quotient T.target.val ≃ Quotient E.val :=
  Setoid.quotientKerEquivOfSurjective T.label T.label_surjective
noncomputable def quotientEquiv : Quotient E.val ≃ Quotient T.target.val := T.labelEquiv.symm

@[simp] theorem labelEquiv_mk (y : B) : T.labelEquiv (Quotient.mk'' y) = T.label y := rfl
theorem quotientEquiv_edge {x : A} {y : B} (h : R x y) :
    T.quotientEquiv (Quotient.mk'' x) = Quotient.mk'' y := by
  apply T.labelEquiv.injective
  simpa only [quotientEquiv,Equiv.apply_symm_apply,labelEquiv_mk] using (T.label_edge h).symm

theorem quotientEquiv_equivariant (g : G) (q : Quotient E.val) :
    T.quotientEquiv (E.act g q) = T.target.act g (T.quotientEquiv q) := by
  induction q using Quotient.inductionOn with
  | _ x =>
    obtain ⟨y,hy⟩ := T.serial x
    rw [T.quotientEquiv_edge hy,InvEq.act_mk,InvEq.act_mk,
      T.quotientEquiv_edge (T.invariant g x y hy)]

end Transport
end CCO.QuotientTransport
