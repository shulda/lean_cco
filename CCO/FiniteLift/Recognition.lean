import CCO.FiniteLift.Kernel
import CCO.Owners.Provider.ExactLift

/-! C11–C14: recognizable finite partial maps, the honest full finite
quotient action, and one simultaneous two-sort lift on a fixed full
preimage. The reused request utility invokes only the accepted RAW
source joint-lifting theorem; no owner EPPA/provider conclusion occurs. -/

universe v w t
namespace CCO.FiniteLift
open RawExact Owners.Product Owners.Provider

section Pure
variable {G A Q : Type*} [Group G] [MulAction G A] [MulAction G Q]

def fullPreimage (π : A → Q) (B : Set Q) : Set A := π ⁻¹' B

def fullProjection (π : A → Q) (B : Set Q) : fullPreimage π B → B :=
  fun x => ⟨π x.val,x.property⟩

theorem fullProjection_onto (π : A → Q) (onto : Function.Surjective π) (B : Set Q) :
    Function.Surjective (fullProjection π B) := by
  intro b
  obtain ⟨x,hx⟩ := onto b.val
  exact ⟨⟨x,by change π x ∈ B; rw [hx]; exact b.property⟩,Subtype.ext hx⟩

def fullQuotient (π : A → Q) (onto : Function.Surjective π)
    (equivπ : ∀ (g : G) x, π (g • x) = g • π x) (B : Set Q) :
    OrbitalQuotient (G := G) (Subtype.val : fullPreimage π B → A)
      (Subtype.val : B → Q) where
  ambient := π
  equivariant := equivπ
  projection := fullProjection π B
  surjective := fullProjection_onto π onto B
  target_injective := Subtype.val_injective
  commutes _ := rfl

/-- C11: both the kernel and EVERY quotient colour are recognized.
This is the actual sparse projected domain; no representative section
or complete-domain hypothesis is imposed on the original partial map. -/
noncomputable def projectedPartial (π : A → Q) (onto : Function.Surjective π)
    (equivπ : ∀ (g : G) x, π (g • x) = g • π x) (B : Set Q)
    (p : OrbitalPartial (G := G) (Subtype.val : fullPreimage π B → A)) :
    OrbitalPartial (G := G) (Subtype.val : B → Q) :=
  (fullQuotient π onto equivπ B).projectedPartial p

/-- C12: the homomorphism has FULL finite structural automorphism
groups on both sides; it is neither a chosen subgroup nor an assertion
that all quotient automorphisms lift globally. -/
noncomputable def finiteAction (π : A → Q) (onto : Function.Surjective π)
    (equivπ : ∀ (g : G) x, π (g • x) = g • π x) (B : Set Q) :
    OrbitalAut G A (Subtype.val : fullPreimage π B → A) →*
      OrbitalAut G Q (Subtype.val : B → Q) :=
  (fullQuotient π onto equivπ B).action

@[simp] theorem finiteAction_projection (π : A → Q) (onto : Function.Surjective π)
    (equivπ : ∀ (g : G) x, π (g • x) = g • π x) (B : Set Q)
    (α : OrbitalAut G A (Subtype.val : fullPreimage π B → A))
    (x : fullPreimage π B) :
    (finiteAction π onto equivπ B α).val (fullProjection π B x) =
      fullProjection π B (α.val x) :=
  (fullQuotient π onto equivπ B).action_projection α x

end Pure

variable {A : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A] [Countable A]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable (K : ExactKernel S G)

include H cco

/-- The whole real map and the ENTIRE finite K-quotient action are
lifted simultaneously, preserving this same full preimage for every
request. In particular, K=Id is permitted. -/
theorem full_preimage_lift (B : Set K.Q)
    (finiteB : B.Finite) (finiteD : (fullPreimage K.proj B).Finite)
    (p : OrbitalPartial (G := G) (Subtype.val : fullPreimage K.proj B → A))
    (β : OrbitalAut G K.Q (Subtype.val : B → K.Q))
    (compatible : ∀ x : p.domain,
      K.proj (p.map x).val = (β.val (fullProjection K.proj B x.val)).val) :
    ∃ α : OrbitalAut G A (Subtype.val : fullPreimage K.proj B → A),
      p.Extends α ∧ finiteAction K.proj K.onto K.proj_smul B α = β := by
  classical
  letI : Finite B := finiteB.to_subtype
  letI : Finite (fullPreimage K.proj B) := finiteD.to_subtype
  let r : OwnerRequest (G := G) K.proj (fullPreimage K.proj B) B
      (fun x => x.property) := ⟨p,β,compatible⟩
  obtain ⟨g,hp,hβ⟩ := exact_ambient_lift S H cco K.proj K.onto K.proj_smul
    K.exact K.kernel (fullPreimage K.proj B) B (fun x => x.property) r
  have hgD : ∀ x : fullPreimage K.proj B, g.val x.val ∈ fullPreimage K.proj B := by
    intro x
    change K.proj (g.val x.val) ∈ B
    rw [hβ x.val x.property]
    exact (β.val ⟨K.proj x.val,x.property⟩).property
  let α : OrbitalAut G A (Subtype.val : fullPreimage K.proj B → A) :=
    restrictAut g (fullPreimage K.proj B) hgD
  refine ⟨α,?_,?_⟩
  · intro x
    apply Subtype.ext
    exact hp x
  · apply Subtype.ext
    apply Equiv.ext
    intro b
    obtain ⟨x,rfl⟩ := fullProjection_onto K.proj K.onto B b
    rw [finiteAction_projection]
    apply Subtype.ext
    exact hβ x.val x.property

end CCO.FiniteLift
