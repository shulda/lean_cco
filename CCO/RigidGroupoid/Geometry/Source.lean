import CCO.RigidGroupoid.Geometry.Correspondence
import CCO.RigidGroupoid.Geometry.Endpoint
import CCO.RigidGroupoid.Geometry.QuotientDominance

/-! Closed providers for the original homogeneous CCO source and its LITERAL
simultaneous quotients. No quotient homogeneity/CCO theorem, section, SAP,
finite-index parity provider or general reverse mixed exact descent is assumed.
Projected-gate exactness remains precisely the explicit A05 hypothesis. -/

universe u v w t
namespace CCO.RigidGroupoid.Geometry
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{u,v,max u v,w} S)

noncomputable def sourceGroupoid {i : ι} (A : Kernel S i) :
    CategoryTheory.Groupoid (Reached S A) :=
  Reached.groupoid H (exactCalculus_of_homogeneous_CCO S H cco)

noncomputable def sourcePointFunctor {i : ι} (A : Kernel S i) :
    letI := sourceGroupoid S H cco A
    CategoryTheory.Functor (Reached S A) (Type v) :=
  Reached.pointFunctor H (exactCalculus_of_homogeneous_CCO S H cco) A

include H cco in
/-- The standing source consumer retains the original countability convention;
the finite bridge arguments actually prove their weaker elementary forms above.
Every structural groupoid/provider in this conclusion is CONSTRUCTED. -/
theorem standing_source_groupoid (_countableSorts : ∀ i, Countable (X i))
    {i : ι} (A : Kernel S i) :
    Nonempty (CategoryTheory.Groupoid.{v} (Reached S A)) ∧ Finite (Reached S A) ∧
      ∀ b c : Reached S A,
        Nonempty (Arrow S (Reached.kernel H (exactCalculus_of_homogeneous_CCO S H cco) b)
          (Reached.kernel H (exactCalculus_of_homogeneous_CCO S H cco) c)) ∧
        Finite (Arrow S (Reached.kernel H (exactCalculus_of_homogeneous_CCO S H cco) b)
          (Reached.kernel H (exactCalculus_of_homogeneous_CCO S H cco) c)) := by
  refine ⟨⟨sourceGroupoid S H cco A⟩,inferInstance,?_⟩
  intro b c
  exact ⟨Reached.connected H (exactCalculus_of_homogeneous_CCO S H cco) b c,
    arrowFinite S H _ _⟩

namespace Canonical
open RawExact

variable {S}
noncomputable def words (F : ∀ i, Kernel S i) (i : ι) : NonemptyExact S i i :=
  Classical.choose (F i).exact

theorem words_relation (F : ∀ i, Kernel S i) (i : ι) :
    evaluate S (words F i).words = (F i).rel := Classical.choose_spec (F i).exact

abbrev Carrier (F : ∀ i, Kernel S i) (i : ι) := (F i).Class

def projection (F : ∀ i, Kernel S i) (i : ι) : X i → Carrier F i := (F i).project

theorem onto (F : ∀ i, Kernel S i) (i : ι) : Function.Surjective (projection F i) :=
  Quotient.mk_surjective

@[instance_reducible] noncomputable def actions (F : ∀ i, Kernel S i) (i : ι) :
    MulAction G (Carrier F i) :=
  ExactCRT.CanonicalTyped.action S H (fun i => (F i).setoid) (words F) (words_relation F) i

theorem equivariant (F : ∀ i, Kernel S i) :
    letI : ∀ i, MulAction G (Carrier F i) := actions H F
    ∀ i (g : G) x, projection F i (g • x) = g • projection F i x := by
  intro i g x
  rfl

theorem kernel_words (F : ∀ i, Kernel S i) (i : ι) :
    GroupActions.kernel (projection F i) = evaluate S (words F i).words := by
  rw [words_relation]
  funext x y
  exact propext Quotient.eq

noncomputable def source (F : ∀ i, Kernel S i) : AtomicSource ι (Carrier F) :=
  ExactCRT.CanonicalTyped.source S H (fun i => (F i).setoid) (words F) (words_relation F)

theorem actual_colours (F : ∀ i, Kernel S i) :
    letI : ∀ i, MulAction G (Carrier F i) := actions H F
    ∀ {i j} (x : Carrier F i) (y : Carrier F j) (x' : Carrier F i) (y' : Carrier F j),
      (source H F).colour x y = (source H F).colour x' y' ↔
        GroupActions.orbital (G := G) x y x' y' := by
  letI : ∀ i, MulAction G (Carrier F i) := actions H F
  letI := S.finiteSort
  intro i j x y x' y'
  exact ExactCRT.TypedPalette.source_colour_eq_iff_orbital _ S H id
    (projection F) (onto F) (equivariant H F) x y x' y'

include cco in
theorem calculus (F : ∀ i, Kernel S i) : ExactCalculus (source H F) :=
  Quotient.canonicalExactCalculus S H cco (fun i => (F i).setoid) (words F) (words_relation F)

def nested (F A : ∀ i, Kernel S i) (hFA : ∀ i, F i ≤ A i) :
    ∀ i x y, projection F i x = projection F i y → (A i).rel x y := by
  intro i x y hxy
  exact hFA i (Quotient.exact hxy)

def endpointNested (F : ∀ i, Kernel S i) {i : ι} (A : Kernel S i) (hFA : F i ≤ A) :
    ∀ x y, projection F i x = projection F i y → A.rel x y := by
  intro x y hxy
  exact hFA (Quotient.exact hxy)

/-- Standalone C16/C17 with ONLY endpoint A05 premises. No coarse gate or
projected-gate exactness at any other named sort is required. -/
noncomputable def endpointArrowEquiv (F : ∀ i, Kernel S i) {i j : ι}
    (A : Kernel S i) (B : Kernel S j) (ha : F i ≤ A) (hb : F j ≤ B)
    (hAq : FullExact (source H F)
      (A.projectedSetoid (projection F i) (onto F i) (endpointNested F A ha)).r)
    (hBq : FullExact (source H F)
      (B.projectedSetoid (projection F j) (onto F j) (endpointNested F B hb)).r) :
    Arrow S A B ≃ Arrow (source H F)
      (A.projectedKernel (source H F) (projection F i) (onto F i) (endpointNested F A ha) hAq)
      (B.projectedKernel (source H F) (projection F j) (onto F j) (endpointNested F B hb) hBq) := by
  letI : ∀ i, MulAction G (Carrier F i) := actions H F
  exact Endpoint.arrowEquiv S (source H F) H cco (projection F) (onto F)
    (equivariant H F) (words F) (kernel_words F) (actual_colours H F)
    A B (endpointNested F A ha) (endpointNested F B hb) hAq hBq

noncomputable def gates (F A : ∀ i, Kernel S i) (hFA : ∀ i, F i ≤ A i)
    (hProjected : ∀ i, FullExact (source H F)
      ((A i).projectedSetoid (projection F i) (onto F i) (nested F A hFA i)).r) :=
  Projected.gate S (source H F) (projection F) (onto F) A (nested F A hFA) hProjected

/-- C16–18 on the actual literal simultaneous quotients. A05 is the ONLY
additional quotient exactness assumption; all other source providers close.
-/
noncomputable def bridgeGroupoidIso (F A : ∀ i, Kernel S i) (hFA : ∀ i, F i ≤ A i)
    (hProjected : ∀ i, FullExact (source H F)
      ((A i).projectedSetoid (projection F i) (onto F i) (nested F A hFA i)).r) :
    BridgeGroupoidIso S (source H F) A (gates H F A hFA hProjected)
      (exactCalculus_of_homogeneous_CCO S H cco) (calculus H cco F) := by
  letI : ∀ i, MulAction G (Carrier F i) := actions H F
  exact Projected.groupoidIso S (source H F) H cco (projection F) (onto F)
    (equivariant H F) (words F) (kernel_words F) (actual_colours H F)
    A (nested F A hFA) hProjected (exactCalculus_of_homogeneous_CCO S H cco)

/-- Quotienting at the bridge objects' own gates makes each projected gate
actual quotient equality. Thus A05 is genuinely DISCHARGED in this consumer.
-/
theorem own_gate_relation (F : ∀ i, Kernel S i) (i : ι) :
    Quotient.image (projection F i) (projection F i) (F i).rel =
      TRel.ident (Carrier F) i := by
  have h := Quotient.image_pullback (projection F i) (projection F i) (onto F i) (onto F i)
    (TRel.ident (Carrier F) i)
  have hk : GroupActions.kernel (projection F i) = (F i).rel :=
    (kernel_words F i).trans (words_relation F i)
  change Quotient.image (projection F i) (projection F i)
    (GroupActions.kernel (projection F i)) = _ at h
  rwa [hk] at h

theorem own_projected_exact (F : ∀ i, Kernel S i) (i : ι) :
    FullExact (source H F)
      ((F i).projectedSetoid (projection F i) (onto F i) (nested F F (fun _ => le_rfl) i)).r := by
  change FullExact (source H F) (Quotient.image (projection F i) (projection F i) (F i).rel)
  rw [own_gate_relation F i]
  exact fullExact_identity (source H F) i

noncomputable def ownGateGroupoidIso (F : ∀ i, Kernel S i) :=
  bridgeGroupoidIso H cco F F (fun _ => le_rfl) (own_projected_exact H F)

include cco in
/-- C04's SAFE direction on the literal quotients, without TI or A05. -/
theorem upwardExact (F : ∀ i, Kernel S i) {i j : ι}
    {D : TRel (Carrier F) i j} (hD : FullExact (source H F) D) :
    FullExact S (GroupActions.pullback (projection F i) (projection F j) D) := by
  obtain ⟨P,hP⟩ := hD
  refine ⟨ExactCRT.CanonicalTyped.exactPullback S H (fun i => (F i).setoid)
    (words F) (words_relation F) cco P,?_⟩
  exact (ExactCRT.CanonicalTyped.exactPullback_relation S H (fun i => (F i).setoid)
    (words F) (words_relation F) cco P).trans
    (congrArg (GroupActions.pullback (projection F i) (projection F j)) hP)

include cco in
/-- C14 actual quotient dominance with all action/palette/word providers closed.
The quotient word may visit ANY named quotient sort of this full exact family.
-/
theorem dominant_on_actual_quotient (F : ∀ i, Kernel S i) {i : ι}
    (t : Arrow S (F i) (F i)) (hd : Dominant (F i) t)
    (Z : Setoid (Carrier F i)) (hZ : FullExact (source H F) Z.r) (hne : Z ≠ ⊥) :
    ∀ x y, Quotient.image (projection F i) (projection F i) t.rel x y → Z x y := by
  letI : ∀ i, MulAction G (Carrier F i) := actions H F
  exact quotient_dominant S (source H F) H cco (projection F) (onto F)
    (equivariant H F) (words F) (kernel_words F) (actual_colours H F) (F i) t hd
    ((kernel_words F i).trans (words_relation F i)) Z hZ hne

theorem nonidentity_actual_quotient_atom (F : ∀ i, Kernel S i) {i : ι}
    (t : Arrow S (F i) (F i)) (hne : t ≠ Arrow.id (F i)) :
    ∃ a : (source H F).Atom i i,
      Quotient.image (projection F i) (projection F i) t.rel = (source H F).atomRel a := by
  letI : ∀ i, MulAction G (Carrier F i) := actions H F
  exact coarse_nonidentity_diversity S (source H F) H (projection F) (onto F)
    (equivariant H F) (words F) (kernel_words F) (actual_colours H F) (F i) t
    ((kernel_words F i).trans (words_relation F i)) hne

end Canonical
end CCO.RigidGroupoid.Geometry
