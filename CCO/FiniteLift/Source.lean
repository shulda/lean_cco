import CCO.FiniteLift.ClosureSource
import CCO.FiniteLift.SafeSpan
import CCO.FiniteLift.OwnerBounds
import CCO.FiniteLift.RelativeRoots

/-! C27: the four BRANCH-SCOPED conclusions of lem:acf-finite-lift.
The ordinary supplied-witness transfer remains independent of H, owner
kernel conditions and any age-level ordinary EPPA hypothesis. -/

universe v w t
namespace CCO.FiniteLift
open Owners.Product OwnerCover RawExact CanonicalQuotients
variable {A : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A] [Countable A]
variable (HS : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable (K : ExactKernel S G)

theorem palette_relation (safe : Set (S.Atom () ())) :
    quotientSafePalette S K safe = quotientSafe K.proj (S.menuRel safe) := by
  funext c d
  exact propext (quotientSafePalette_iff S K safe c d)

include HS cco

theorem ordinary_source (finiteK : K.FiniteClasses)
    (safe : Set (S.Atom () ())) (A0 : Set A) (finiteA : A0.Finite) (nonemptyA : A0.Nonempty)
    (Dbar : Set K.Q)
    (w : OrdinaryWitness (G := G) (aclSet (FullAut G K.Q))
      (quotientSafePalette S K safe) (K.proj '' A0) Dbar) :
    OrdinaryWitness (G := G) (aclSet G) (S.menuRel safe) A0 (K.proj ⁻¹' Dbar) := by
  rw [palette_relation S K safe] at w
  exact ordinary_reconstruction S HS cco K finiteK (S.menuRel safe) A0 finiteA nonemptyA Dbar w

theorem relative_source (finiteK : K.FiniteClasses)
    (safe : Set (S.Atom () ())) (A0 : Set A) (finiteA : A0.Finite) (nonemptyA : A0.Nonempty)
    (H : ExactKernel S G) (Dbar : Set K.Q) (Bbar : Set (J S HS cco K H).Q)
    (finiteBbar : Bbar.Finite) (imageD : rK S HS cco K H '' Dbar = Bbar)
    (onto : Function.Surjective (ownerAction S HS cco K H Bbar))
    (fibres : GroupActions.FibreTransitive (ownerAction S HS cco K H Bbar)
      (fun b : ((rH S HS cco K H) ⁻¹' Bbar) => fullProjection (rH S HS cco K H) Bbar b))
    (w : RelativeWitness (quotientOwner S HS cco K H Dbar Bbar imageD)
      (aclSet (FullAut G K.Q)) (quotientSafePalette S K safe) (K.proj '' A0)) :
    RelativeWitness (realOwner S HS cco K H Dbar Bbar imageD)
      (aclSet G) (S.menuRel safe) A0 := by
  rw [palette_relation S K safe] at w
  exact relative_reconstruction S HS cco K H finiteK (S.menuRel safe) A0 finiteA
    nonemptyA Dbar Bbar finiteBbar imageD onto fibres w

/-- Actual source conclusions, with every extra premise confined to its
proper branch. This does not construct a supplied quotient EPPA witness. -/
structure FiniteReconstruction (safe : Set (S.Atom () ())) : Prop where
  standing : SourceProperties.{v,w,t,v} S HS K.quotientData
  finite_closures : ∀ (A0 : Set A), A0.Finite →
    (aclSet (FullAut G A) A0).Finite ∧
      (aclSet (FullAut G K.Q) (K.proj '' A0)).Finite
  closure_identity : ∀ (A0 : Set A), A0.Finite →
    aclSet (FullAut G A) A0 = K.proj ⁻¹' aclSet (FullAut G K.Q) (K.proj '' A0)
  safe_descent : StrongClosedAmalgamation G (aclSet G) (S.menuRel safe) →
    StrongClosedAmalgamation (FullAut G K.Q) (aclSet (FullAut G K.Q))
      (quotientSafePalette S K safe)
  ordinary : ∀ (A0 : Set A), A0.Finite → A0.Nonempty → ∀ (Dbar : Set K.Q),
    OrdinaryWitness (G := G) (aclSet (FullAut G K.Q))
      (quotientSafePalette S K safe) (K.proj '' A0) Dbar →
    OrdinaryWitness (G := G) (aclSet G) (S.menuRel safe) A0 (K.proj ⁻¹' Dbar)
  relative : ∀ (A0 : Set A), A0.Finite → A0.Nonempty →
    ∀ (H : ExactKernel S G) (Dbar : Set K.Q) (Bbar : Set (J S HS cco K H).Q)
      (finiteBbar : Bbar.Finite) (imageD : rK S HS cco K H '' Dbar = Bbar),
    Function.Surjective (ownerAction S HS cco K H Bbar) →
    GroupActions.FibreTransitive (ownerAction S HS cco K H Bbar)
      (fun b : ((rH S HS cco K H) ⁻¹' Bbar) => fullProjection (rH S HS cco K H) Bbar b) →
    RelativeWitness (quotientOwner S HS cco K H Dbar Bbar imageD)
      (aclSet (FullAut G K.Q)) (quotientSafePalette S K safe) (K.proj '' A0) →
    RelativeWitness (realOwner S HS cco K H Dbar Bbar imageD)
      (aclSet G) (S.menuRel safe) A0

/-- The source finite exact reconstruction lemma, all local providers
discharged. No SAP, finite normalization, thin packets, same-rank master,
global quotient group section or ordinary EPPA(Q) premise remains. -/
theorem finite_lift (finiteK : K.FiniteClasses) (safe : Set (S.Atom () ())) :
    FiniteReconstruction S HS cco K safe where
  standing := K.standing_source HS cco
  finite_closures := by
    intro A0 finiteA
    rw [aclSet_full_eq S HS A0 finiteA]
    exact ⟨aclSet_finite G S HS A0 finiteA,
      K.quotient_acl_finite HS cco finiteK _ (finiteA.image K.proj)⟩
  closure_identity := K.acl_pullback_full HS cco finiteK
  safe_descent := K.strongClosedSafePalette HS cco finiteK safe
  ordinary := ordinary_source S HS cco K finiteK safe
  relative := relative_source S HS cco K finiteK safe

/-- A caller can supply just the actual relation and its exact word
presentation: source invariance is constructed, not left as a provider. -/
theorem finite_lift_of_exact (R : Setoid A) (E : NonemptyExact S () ())
    (represents : evaluate S E.words = R.r)
    (finiteR : ∀ a : A, {b | R a b}.Finite) (safe : Set (S.Atom () ())) :
    FiniteReconstruction S HS cco (ExactKernel.ofExact HS R E represents) safe :=
  finite_lift S HS cco (ExactKernel.ofExact HS R E represents) finiteR safe

end CCO.FiniteLift
