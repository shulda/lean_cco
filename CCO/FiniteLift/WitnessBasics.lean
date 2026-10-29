import CCO.FiniteLift.Palette
import CCO.FiniteLift.Recognition
import CCO.FiniteLift.ClosureOrbit

/-! Literal finite rooted witnesses and unsafe projection as a SET of
distinct classes. A singleton is unsafe vacuously; no injectivity of the
projection on a clique is assumed. -/

namespace CCO.FiniteLift
open Owners.Product

def Unsafe {A : Type*} (safe : A → A → Prop) (Z : Set A) : Prop :=
  Z.Nonempty ∧ ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → ¬ safe x y

theorem unsafe_image {A Q : Type*} (π : A → Q) (safe : A → A → Prop)
    {Z : Set A} (hZ : Unsafe safe Z) : Unsafe (quotientSafe π safe) (π '' Z) := by
  refine ⟨hZ.1.image π,?_⟩
  rintro c ⟨x,hx,rfl⟩ d ⟨y,hy,rfl⟩ hne hsafe
  have hxy : x ≠ y := fun h => hne (congrArg π h)
  exact hZ.2 x hx y hy hxy (hsafe.2 x y rfl rfl)

/-- A genuine empty/singleton projection causes no exception. -/
theorem unsafe_singleton {A : Type*} (safe : A → A → Prop) (a : A) :
    Unsafe safe {a} := by
  refine ⟨Set.singleton_nonempty a,?_⟩
  intro x hx y hy hne
  exact False.elim (hne ((Set.mem_singleton_iff.mp hx).trans
    (Set.mem_singleton_iff.mp hy).symm))

theorem unsafe_mono {A : Type*} {safe safe' : A → A → Prop}
    (h : ∀ x y, safe' x y → safe x y) {Z : Set A}
    (hZ : Unsafe safe Z) : Unsafe safe' Z :=
  ⟨hZ.1,fun x hx y hy hne hs => hZ.2 x hx y hy hne (h x y hs)⟩

theorem unsafe_fullProjection {A Q : Type*} (π : A → Q)
    (B : Set Q) (safe : A → A → Prop)
    {Z : Set (fullPreimage π B)}
    (hZ : Unsafe (fun x y : fullPreimage π B => safe x.val y.val) Z) :
    Unsafe (fun c d : B => quotientSafe π safe c.val d.val)
      (fullProjection π B '' Z) := by
  have hi := unsafe_image (fullProjection π B)
    (fun x y : fullPreimage π B => safe x.val y.val) hZ
  apply unsafe_mono ?_ hi
  intro c d h
  refine ⟨fun he => h.1 (congrArg Subtype.val he),?_⟩
  intro x y hx hy
  exact h.2 x.val y.val (congrArg Subtype.val hx) (congrArg Subtype.val hy)

variable {G A : Type*} [Group G] [MulAction G A]

/-- Every request is a partial map on the displayed finite witness whose
domain AND range lie in the actual input A0. The rooted conclusion moves
the selected ORIGINAL point into A0 itself. -/
structure OrdinaryWitness (cl : Set A → Set A) (safe : A → A → Prop) (A0 D : Set A) : Prop where
  finite : D.Finite
  closure : cl A0 ⊆ D
  extensions : EPPAFor (G := G) (ι := (Subtype.val : D → A)) {x | x.val ∈ A0}
  roots : ∀ (Z : Set D), Unsafe (fun x y : D => safe x.val y.val) Z →
    ∀ z ∈ Z, ∃ α : OrbitalAut G A (Subtype.val : D → A),
      (∀ x ∈ Z, (α.val x).val ∈ cl A0) ∧ (α.val z).val ∈ A0

end CCO.FiniteLift
