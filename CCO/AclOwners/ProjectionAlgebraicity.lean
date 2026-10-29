import CCO.AclOwners.ProjectionLifting
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Set.Finite.Lattice

/-! The converse to exact algebraicity projection is a finite-fibre
argument. It requires no compatible-tuple realization or CRT surjectivity. -/
universe v w t z q
namespace CCO.AclOwners
open RealClosure.Bounds ParityHasse.Original FinitePackets.Normalization RawExact

section FiniteFibres
variable {M : Type v} {I : Type z} [Finite I] {Q : I → Type q}

/-- Finite coordinate images and finite ACTUAL common-kernel classes
make a set finite, including the empty coordinate family. -/
theorem finite_of_finite_joint_images (π : ∀ i, M → Q i) (K : Setoid M)
    (hK : ∀ x y, K x y ↔ ∀ i, π i x = π i y)
    (hfib : ∀ x, Finite {y // K x y}) (U : Set M)
    (himage : ∀ i, (π i '' U).Finite) : U.Finite := by
  let f : M → ∀ i, Q i := fun x i => π i x
  have hp : {q : ∀ i, Q i | ∀ i, q i ∈ π i '' U}.Finite := Set.Finite.pi' himage
  have hi : (f '' U).Finite := hp.subset (by
    rintro q ⟨x,hx,rfl⟩ i
    exact ⟨x,hx,rfl⟩)
  apply Set.Finite.of_finite_fibers f hi
  rintro q ⟨x,hx,rfl⟩
  have hc : {y | K x y}.Finite := Set.finite_coe_iff.mp (hfib x)
  apply hc.subset
  rintro y ⟨_,hy⟩
  apply (hK x y).mpr
  intro i
  exact (congrFun (Set.mem_singleton_iff.mp hy) i).symm

variable {G : Type t} [Group G] [MulAction G M] [∀ i, MulAction G (Q i)]

/-- Any equivariant finite-kernel family recovers real algebraicity.
The coordinate groups may be replaced by larger full groups via inclusion;
only finite coordinate orbits, never a global lifting, are needed. -/
theorem algebraic_of_finite_joint_kernel [DecidableEq M] [∀ i, DecidableEq (Q i)]
    (π : ∀ i, M → Q i) (equiv : ∀ i (g : G) x, π i (g • x) = g • π i x)
    (K : Setoid M) (hK : ∀ x y, K x y ↔ ∀ i, π i x = π i y)
    (hfib : ∀ x, Finite {y // K x y}) (A : Finset M) (x : M)
    (hx : ∀ i, π i x ∈ Acl G (A.image (π i))) : x ∈ Acl G A := by
  apply finite_of_finite_joint_images π K hK hfib (orbitOver G A x)
  intro i
  apply (hx i).subset
  rintro y ⟨z,⟨g,hg,rfl⟩,rfl⟩
  refine ⟨g,?_,(equiv i g x).symm⟩
  intro a ha
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
  rw [← equiv,hg b hb]
end FiniteFibres

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)

/-- The common kernel is the ACTUAL meet of the indexed equivalences. -/
def jointKernel {I : Type z} (J : I → ColourEq S ()) : Setoid M where
  r x y := ∀ i, J i x y
  iseqv := ⟨fun x i => (J i).val.refl x,
    fun h i => (J i).val.symm (h i),fun h k i => (J i).val.trans (h i) (k i)⟩

/-- General finite-meet closure pullback, including repeated kernels
and empty families when their common Top kernel really has finite classes. -/
theorem exact_closure_pullback [Countable M] [DecidableEq M]
    (cco : SemanticCCO.{0,v,0,w} S) {I : Type z} [Finite I]
    (J : I → ColourEq S ()) (B : ∀ _ : I, NonemptyExact S () ())
    (hB : ∀ i, evaluate S (B i).words = (J i).val.r)
    (hfib : ∀ x, Finite {y // jointKernel S J x y}) (A : Finset M) :
    letI : ∀ i, MulAction G (Quotient (J i).val) := fun i => originalQuotientAction S H (J i)
    letI : ∀ i, DecidableEq (Quotient (J i).val) := fun _ => Classical.decEq _
    Acl G A = {x | ∀ i, (Quotient.mk'' x : Quotient (J i).val) ∈
      Acl G (A.image Quotient.mk'')} := by
  classical
  letI : ∀ i, MulAction G (Quotient (J i).val) := fun i => originalQuotientAction S H (J i)
  letI : ∀ i, DecidableEq (Quotient (J i).val) := fun _ => Classical.decEq _
  ext x
  constructor
  · intro hx i
    exact exact_projection_algebraic S H (J i) (B i) (hB i) cco A x hx
  · intro hx
    exact algebraic_of_finite_joint_kernel (fun i => (Quotient.mk'' : M → Quotient (J i).val))
      (fun i => quotient_projection_equivariant S H (J i)) (jointKernel S J)
      (fun x y => by
        change (∀ i, J i x y) ↔ ∀ i, (Quotient.mk'' x : Quotient (J i).val) = Quotient.mk'' y
        simp only [Quotient.eq]) hfib A x hx
end CCO.AclOwners
