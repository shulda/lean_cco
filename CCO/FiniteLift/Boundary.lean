import CCO.FiniteLift.Source

/-! Identity kernels, empty closure inputs and singleton unsafe images
are actual allowed cases of the source theorem, not excluded conventions. -/

universe v w t
namespace CCO.FiniteLift
open RawExact
variable {A : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A]
variable (HS : HomogeneousSource S G)

def identityKernel : ExactKernel S G := ExactKernel.ofExact HS ⊥ (exactIdentityAtom S ()) (by
  rw [exactIdentityAtom_relation S ()]
  rfl)

theorem identityKernel_finite : (identityKernel S HS).FiniteClasses := by
  intro a
  apply (Set.finite_singleton a).subset
  intro b hb
  exact Set.mem_singleton_iff.mpr hb.symm

theorem identityKernel_projection_injective : Function.Injective (identityKernel S HS).proj := by
  intro x y h
  exact ((identityKernel S HS).proj_eq x y).mp h

/-- The actual identity quotient is canonically the original real sort. -/
def identityKernelEquiv : (identityKernel S HS).Q ≃ A :=
  CanonicalQuotients.identityEquiv (identityKernel S HS).rel (fun _ _ => Iff.rfl)

@[simp] theorem identityKernelEquiv_proj (a : A) :
    identityKernelEquiv S HS ((identityKernel S HS).proj a) = a := rfl

theorem identity_finite_lift [Countable A] (cco : SemanticCCO.{0,v,v,w} S)
    (safe : Set (S.Atom () ())) : FiniteReconstruction S HS cco (identityKernel S HS) safe :=
  finite_lift S HS cco (identityKernel S HS) (identityKernel_finite S HS) safe

include HS

theorem empty_acl_pullback [Countable A] (cco : SemanticCCO.{0,v,v,w} S)
    (K : ExactKernel S G) (finiteK : K.FiniteClasses) :
    aclSet (FullAut G A) ∅ = K.proj ⁻¹' aclSet (FullAut G K.Q) ∅ := by
  simpa only [Set.image_empty] using K.acl_pullback_full HS cco finiteK ∅ Set.finite_empty

end CCO.FiniteLift
