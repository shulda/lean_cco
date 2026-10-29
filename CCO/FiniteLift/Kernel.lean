import CCO.RawExact.CanonicalQuotientInheritance
import CCO.RawExact.QuotientFiniteHomogeneity
import CCO.RawExact.ActualNestedMaps
import CCO.Owners.Product.SparseDescent
import Mathlib.Algebra.Group.Action.End

/-! B029: actual full exact kernels, their literal quotient maps and the
full automorphism group of the named orbital language. Finite fibres are
an additional property of K, not an assumption on the later owner H. -/

universe v w t
namespace CCO.FiniteLift
open RawExact Owners.Product

abbrev FullAut (G : Type*) [Group G] (A : Type*) [MulAction G A] :=
  OrbitalAut G A (id : A → A)

def ambientAut {G A : Type*} [Group G] [MulAction G A] (g : G) : FullAut G A :=
  ⟨MulAction.toPerm g, (mem_orbitalAut_iff _).mpr (fun _ _ => ⟨g,rfl,rfl⟩)⟩

/-- Naming all old pair orbitals makes the full structure group have
EXACTLY the same pair orbitals. Its full stabilizers need not be the old
group's full ambient image. -/
theorem full_orbital_iff {G A : Type*} [Group G] [MulAction G A]
    (x y x' y' : A) :
    GroupActions.orbital (G := FullAut G A) x y x' y' ↔
      GroupActions.orbital (G := G) x y x' y' := by
  constructor
  · rintro ⟨g,rfl,rfl⟩
    exact orbitalAut_pair g x y
  · rintro ⟨g,rfl,rfl⟩
    exact ⟨ambientAut g,rfl,rfl⟩

variable {A : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable (G : Type t) [Group G] [MulAction G A]

/-- The relation itself is full exact. No greatest-finite-equivalence,
thinness, properness or finite-fibre premise is included. -/
structure ExactKernel where
  rel : Setoid A
  exact : NonemptyExact S () ()
  represents : evaluate S exact.words = rel.r
  invariant : ∀ (g : G) x y, rel x y → rel (g • x) (g • y)

namespace ExactKernel
variable {S G} (K : ExactKernel S G)

abbrev Q := Quotient K.rel

instance quotientInvariant : CanonicalQuotients.Invariant G K.rel := ⟨K.invariant⟩

instance quotientAction : MulAction G K.Q :=
  CanonicalQuotients.quotientMulAction K.rel

def proj : A → K.Q := Quotient.mk''

theorem onto : Function.Surjective K.proj := Quotient.mk''_surjective

@[simp] theorem proj_smul (g : G) (a : A) : K.proj (g • a) = g • K.proj a := rfl

theorem kernel : GroupActions.kernel K.proj = evaluate S K.exact.words := by
  rw [K.represents]
  funext x y
  exact propext Quotient.eq

@[simp] theorem proj_eq (a b : A) : K.proj a = K.proj b ↔ K.rel a b := Quotient.eq

def FiniteClasses : Prop := ∀ a : A, {b | K.rel a b}.Finite

/-- Invariance is actually supplied by the source, rather than a new
source-provider obligation. The field above also permits using the pure
quotient utilities without carrying a homogeneous-source proof. -/
def ofExact (H : HomogeneousSource S G) (R : Setoid A)
    (E : NonemptyExact S () ()) (hE : evaluate S E.words = R.r) : ExactKernel S G where
  rel := R
  exact := E
  represents := hE
  invariant := by
    intro g x y h
    rw [← hE] at h ⊢
    exact presentation_invariant_of_homogeneous S H E.words g x y h

/-- A finite quotient embedding, with all canonical orbital names, lifts
to one old-group element on its whole finite domain. This supplies the
maps on full real preimages in closed-span descent. -/
theorem finite_embedding_lift [Countable A]
    (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
    {U : Type*} [Finite U] (ι κ : U → K.Q)
    (hPair : ∀ x y, GroupActions.orbital (G := G) (ι x) (ι y) (κ x) (κ y)) :
    ∃ g : G, ∀ x, g • ι x = κ x := by
  exact finite_quotient_tuple_lifting_of_CCO S H cco
    (fun _ : Unit => K.Q) (fun _ => ()) (fun _ => K.proj)
    (fun _ => K.onto) (fun _ => K.proj_smul)
    (fun _ => K.exact) (fun _ => K.kernel)
    (fun _ : U => ()) ι κ hPair

end ExactKernel
end CCO.FiniteLift
