import CCO.UnaryTermsReturn.CompletedNamedReachability
import Mathlib.Data.Set.Card

/-!
# B052 C13–C15: least closure under genuine terminal named steps

The actual completed real/hidden carrier has the B049 original named
projection, upward-map and RAW quotient-transition primitives. This
module identifies its ONE-GENERATOR unary closure as the *least* set
closed under those literal well-typed primitive edges.

The closure is the reflexive finite-path reachability relation from
the existing named transition graph; it is not the unrestricted
closure of arbitrary total unary operations in a partial source.
In particular, a named primitive never sends a hidden quotient back
to an old real point. Uniform finiteness requires the additional
bridge from these paths back to actual named B049 term values and
then the already proved finite normal-code family. No hidden SAP,
arbitrary-subgroup definability, or external HN theorem is assumed.
-/

universe u v w t

namespace CCO.UnaryTermsReturn

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- Actual unary-functional closure condition on the FULL
represented real-or-hidden terminal carrier: every genuine
well-typed named primitive step stays in the set. -/
def OriginalCompletedNamedStepClosed
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    (C : Set (OriginalCompletedNamedCarrier S H)) : Prop :=
  ∀ ⦃a b : OriginalCompletedNamedCarrier S H⦄,
    a ∈ C → OriginalCompletedNamedStep S H sap nr2 a b → b ∈ C

/-- Every represented hidden vertex is LITERALLY a class of
some existing original named proper FULL quotient coordinate.
There is no separately postulated hidden orbit, section, or real
representative: the witness is the representedness proof already
carried by the completed hidden vertex. -/
theorem original_completed_hidden_value_has_named_witness
    (H : HomogeneousSource S G)
    (v : OriginalCompletedNamedHiddenValue S H) :
    ∃ (i : ι) (D : CCO.TransitionClosure.OriginalNamedHiddenCoordinate S H i)
      (q : Quotient D.val.val),
      (Sum.inr v : OriginalCompletedNamedCarrier S H) =
        originalCompletedNamedHiddenNode S H D q := by
  rcases v with ⟨⟨i, ⟨F, q⟩⟩, ⟨D, hD⟩⟩
  rcases D with ⟨J, hJ⟩
  change J = F at hD
  cases hD
  exact ⟨i, ⟨F, hJ⟩, q, rfl⟩

/-- The ACTUAL one-generated closure under the original
represented terminal primitive edge graph. The empty word
is real/hidden identity and other words are finite paths. -/
def originalCompletedNamedStepClosure
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    (x : OriginalCompletedNamedCarrier S H) :
    Set (OriginalCompletedNamedCarrier S H) :=
  {y | OriginalCompletedNamedReachable S H sap nr2 x y}

/-- The true identity/empty named word keeps the generator
inside its own actual unary closure. -/
theorem original_completed_named_step_closure_contains
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    (x : OriginalCompletedNamedCarrier S H) :
    x ∈ originalCompletedNamedStepClosure S H sap nr2 x :=
  OriginalCompletedNamedReachable.refl x

/-- The named primitive closure is CLOSED under every
genuinely interpreted typed real projection, upward map,
and quotient transition, including all original sort tags. -/
theorem original_completed_named_step_closure_closed
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    (x : OriginalCompletedNamedCarrier S H) :
    OriginalCompletedNamedStepClosed S H sap nr2
      (originalCompletedNamedStepClosure S H sap nr2 x) := by
  intro a b ha e
  exact OriginalCompletedNamedReachable.step ha e

/-- Any other actually named-primitive-closed set containing
the generator contains the WHOLE finite-path closure.
This is the least-closure direction, not a separate axiom
that an arbitrary partial hidden source is completed. -/
theorem original_completed_named_step_closure_minimal
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    (x : OriginalCompletedNamedCarrier S H)
    (C : Set (OriginalCompletedNamedCarrier S H))
    (hx : x ∈ C)
    (hC : OriginalCompletedNamedStepClosed S H sap nr2 C) :
    originalCompletedNamedStepClosure S H sap nr2 x ⊆ C := by
  intro y hy
  induction hy with
  | refl => exact hx
  | step h e ih => exact hC ih e

/-- Exactly the least actually primitive-closed source set
containing x is the closure above. No cardinal estimate is
silently inferred without the genuine B049 word bridge. -/
theorem original_completed_named_step_closure_eq_of_least
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    (x : OriginalCompletedNamedCarrier S H)
    (C : Set (OriginalCompletedNamedCarrier S H))
    (hx : x ∈ C)
    (hC : OriginalCompletedNamedStepClosed S H sap nr2 C)
    (hLeast : ∀ D : Set (OriginalCompletedNamedCarrier S H),
      x ∈ D → OriginalCompletedNamedStepClosed S H sap nr2 D →
      C ⊆ D) :
    C = originalCompletedNamedStepClosure S H sap nr2 x := by
  apply Set.Subset.antisymm
  · exact hLeast _
      (original_completed_named_step_closure_contains S H sap nr2 x)
      (original_completed_named_step_closure_closed S H sap nr2 x)
  · exact original_completed_named_step_closure_minimal
      S H sap nr2 x C hx hC


/-- An actual finite completed unary-closed induced member has
the same named primitive symbols, restricted to its own literal
vertices. Here a restricted path never leaves its actual closed
carrier; no extra completion witness or full hidden SAP is assumed. -/
inductive OriginalCompletedNamedRestrictedReachable
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    (C : Set (OriginalCompletedNamedCarrier S H)) :
    C → C → Prop where
  | refl (x : C) :
      OriginalCompletedNamedRestrictedReachable H sap nr2 C x x
  | step {x y z : C}
      (h : OriginalCompletedNamedRestrictedReachable H sap nr2 C x y)
      (e : OriginalCompletedNamedStep S H sap nr2 y.val z.val) :
      OriginalCompletedNamedRestrictedReachable H sap nr2 C x z

/-- Restricting a path to a completed member does not change
any named primitive value when regarded in the actual ambient
source. This is the direct source-facing path semantics. -/
theorem original_completed_restricted_reachable_sound
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    (C : Set (OriginalCompletedNamedCarrier S H))
    {x y : C}
    (h : OriginalCompletedNamedRestrictedReachable S H sap nr2 C x y) :
    OriginalCompletedNamedReachable S H sap nr2 x.val y.val := by
  induction h with
  | refl => exact .refl _
  | step h e ih => exact .step ih e

/-- Conversely an actual named-primitive-closed member contains
EVERY vertex visited by an ambient path from one of its vertices.
The path lifts to the actual induced member without changing
functions, equalities or adding quotient representatives. -/
theorem original_completed_restricted_reachable_complete
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    (C : Set (OriginalCompletedNamedCarrier S H))
    (hClosed : OriginalCompletedNamedStepClosed S H sap nr2 C)
    (x : C) {y : OriginalCompletedNamedCarrier S H}
    (h : OriginalCompletedNamedReachable S H sap nr2 x.val y) :
    ∃ v : C, v.val = y ∧
      OriginalCompletedNamedRestrictedReachable S H sap nr2 C x v := by
  induction h with
  | refl => exact ⟨x,rfl,.refl x⟩
  | @step b c h e ih =>
      obtain ⟨v,hv,hvReach⟩ := ih
      have e' : OriginalCompletedNamedStep S H sap nr2 v.val c := by
        simpa only [hv] using e
      let z : C := ⟨c,hClosed v.property e'⟩
      exact ⟨z,rfl,.step hvReach e'⟩

/-- Exact source10 completed-substructure clause: the image of
its INTERNAL one-generator unary closure under literal inclusion
equals the AMBIENT one-generator named primitive closure. It
does not infer that an arbitrary partial hidden structure is
an actual unary-closed induced member. -/
theorem original_completed_restricted_reachable_image
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    (C : Set (OriginalCompletedNamedCarrier S H))
    (hClosed : OriginalCompletedNamedStepClosed S H sap nr2 C)
    (x : C) :
    (Subtype.val '' {y : C |
      OriginalCompletedNamedRestrictedReachable S H sap nr2 C x y}) =
        originalCompletedNamedStepClosure S H sap nr2 x.val := by
  ext y
  constructor
  · rintro ⟨v,hv,rfl⟩
    exact original_completed_restricted_reachable_sound
      S H sap nr2 C hv
  · intro hy
    obtain ⟨v,hv,hReach⟩ :=
      original_completed_restricted_reachable_complete
        S H sap nr2 C hClosed x hy
    exact ⟨v,hReach,hv⟩



/-- In the ACTUAL original terminal interpreted language, no
positive unary primitive has a REAL codomain. Consequently
a finite primitive path ending at a real vertex must be
the genuine identity/empty term, not a synthetic STRONG
diagonal relation. The start is literally the same real point. -/
theorem original_completed_named_reachable_real_target
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    {a : OriginalCompletedNamedCarrier S H}
    {y : Sigma X}
    (h : OriginalCompletedNamedReachable S H sap nr2 a (.inl y)) :
    a = .inl y := by
  cases h with
  | refl => rfl
  | step h e => cases e

/-- No orphan quotient generator can reach a real vertex
through the actual terminal primitive vocabulary. It
does not adjoin a representative real root to an orphan
finite completed member. -/
theorem original_completed_named_orphan_no_real
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    (v : OriginalCompletedNamedHiddenValue S H)
    (y : Sigma X) :
    ¬ OriginalCompletedNamedReachable S H sap nr2 (.inr v) (.inl y) := by
  intro h
  have hsrc :=
    original_completed_named_reachable_real_target S H sap nr2 h
  cases hsrc

/-- Literal real equality is the ONLY real-to-real term
value: the actual completed real-source one-generator
closure intersects the real summand in precisely its
source real point. -/
theorem original_completed_named_real_closure_real_iff
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    (x y : Sigma X) :
    (.inl y : OriginalCompletedNamedCarrier S H) ∈
        originalCompletedNamedStepClosure S H sap nr2 (.inl x) ↔
      y = x := by
  constructor
  · intro h
    exact Sum.inl.inj
      (original_completed_named_reachable_real_target S H sap nr2 h).symm
  · intro h
    subst y
    exact OriginalCompletedNamedReachable.refl _



/-- A finite genuine completed member inherits ANY already
established ambient one-generator bound by its literal
closed-induced inclusion. This is the precise finite-age
consumer, not a stand-in for proving the ambient source
bound from B049 named term normal forms. -/
theorem original_completed_restricted_closure_uniform_from_ambient
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    (C : Set (OriginalCompletedNamedCarrier S H))
    (hClosed : OriginalCompletedNamedStepClosed S H sap nr2 C)
    (x : C)
    (m : Nat)
    (hFinite : (originalCompletedNamedStepClosure
      S H sap nr2 x.val).Finite)
    (hBound : (originalCompletedNamedStepClosure
      S H sap nr2 x.val).ncard ≤ m) :
    ({y : C | OriginalCompletedNamedRestrictedReachable
      S H sap nr2 C x y}).ncard ≤ m := by
  letI : Finite ↥(originalCompletedNamedStepClosure
      S H sap nr2 x.val) := hFinite.to_subtype
  have hLe :
      ({y : C | OriginalCompletedNamedRestrictedReachable
        S H sap nr2 C x y}).ncard ≤
        (originalCompletedNamedStepClosure S H sap nr2 x.val).ncard := by
    apply Set.ncard_le_ncard_of_injOn
      (s := {y : C | OriginalCompletedNamedRestrictedReachable
        S H sap nr2 C x y})
      (t := originalCompletedNamedStepClosure S H sap nr2 x.val)
      (fun y : C => y.val)
    · intro y hy
      rw [← original_completed_restricted_reachable_image
        S H sap nr2 C hClosed x]
      exact ⟨y,hy,rfl⟩
    · intro y _ z _ heq
      exact Subtype.ext heq
  exact hLe.trans hBound


end CCO.UnaryTermsReturn
