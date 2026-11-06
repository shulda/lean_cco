import CCO.TypedOrbitFrames.ActualPairwiseHelly
import CCO.TypedOrbitFrames.OriginalFibreMotion
import CCO.RawExact.CanonicalQuotients
import CCO.AclOwners.Avoidance

/-!
# Source11 C34: one actual original action avoids all quotient lists

Each forbidden list consists of actual quotient classes for one original
invariant kernel. The kernels need not be named hidden sorts, and may
include real equality. The action on every quotient is derived from old
colour invariance. The single fibre-avoidance move uses the SAME original
group and the SAME actual full-meet class for every output coordinate.

The only infinite-index premise is the source11 standing FULL strict-cover
assumption, including Top covers. No hidden homogeneity, SAP or quotient
section is assumed. Exact fine one-point spoke colours are not controlled.
-/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Original
open CCO.RealClosure.Bounds

universe u v w r
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i : ι, MulAction G (X i)]

/-- The actual quotient action is constructed from the original homogeneous
source's proved colour invariance, for any FULL original invariant kernel. -/
@[instance_reducible] def originalColourEqQuotientAction
    (H : HomogeneousSource S G) {i : ι} (J : ColourEq S i) :
    MulAction G (Quotient J.val) := by
  letI : RawExact.CanonicalQuotients.Invariant G J.val :=
    ⟨colourInvariant_groupInvariant S H J.property⟩
  exact RawExact.CanonicalQuotients.quotientMulAction J.val

/-- Once one real point of the class incidence fibre is fixed, one common
representative avoids every finite forbidden list on finitely many unforced
actual quotient outputs simultaneously. Even an empty coordinate list is
allowed. The single common motion uses only the accepted I14 finite-action
avoidance theorem, not the separate I16 quotient-fibre provider. -/
theorem original_actual_common_fibre_simultaneous_avoidance
    (H : HomogeneousSource S G)
    {i : ι} (hCover : OriginalAllFullCoversInfinite S (i := i))
    {m n : Nat} (E : Fin m → ColourEq S i) (c : Fin m → X i)
    (x₀ : X i) (hx₀ : x₀ ∈ originalActualClassFibre S E c)
    (J : Fin n → ColourEq S i)
    (hUnforced : ∀ k, ¬ originalActualMeetEquivalence S E ≤ J k)
    (forbidden : ∀ k, Finset (Quotient (J k).val)) :
    ∃ x : X i, x ∈ originalActualClassFibre S E c ∧
      ∀ k, Quotient.mk (J k).val x ∉ forbidden k := by
  classical
  let K : ColourEq S i := originalActualMeetEquivalence S E
  letI : MulAction G (Quotient K.val) := originalColourEqQuotientAction S H K
  letI : ∀ k : Fin n, MulAction G (Quotient (J k).val) :=
    fun k => originalColourEqQuotientAction S H (J k)
  let Q := Sigma (fun k : Fin n => Quotient (J k).val)
  let stabilizer := MulAction.stabilizer G (Quotient.mk K.val x₀)
  let output : Fin n → Q := fun k => ⟨k, Quotient.mk (J k).val x₀⟩
  let moving : Finset Q := Finset.univ.image output
  have hOrbit (k : Fin n) :
      (MulAction.orbit stabilizer (output k)).Infinite := by
    let C := {q : Quotient (J k).val //
      q ∈ originalJClassesWithinHClass S K (J k) x₀}
    letI : Infinite C :=
      original_unforced_J_classes_in_H_fibre_infinite
        S hCover K (J k) (hUnforced k) x₀
    let embed : C → Q := fun q => ⟨k,q.val⟩
    have hEmbed : Function.Injective embed := by
      intro q r h
      apply Subtype.ext
      simpa only [embed, Q, Sigma.mk.injEq, heq_eq_eq, true_and] using h
    apply Set.infinite_of_injective_forall_mem hEmbed
    intro q
    obtain ⟨y,hy,hq⟩ := q.property
    obtain ⟨g,hg⟩ := S.original_sort_transitive_of_homogeneous H i x₀ y
    have hFix : g ∈ stabilizer := by
      change Quotient.mk K.val (g • x₀) = Quotient.mk K.val x₀
      rw [hg]
      exact Quotient.sound (K.val.symm hy)
    refine ⟨⟨g,hFix⟩,?_⟩
    change (⟨k,Quotient.mk (J k).val (g • x₀)⟩ : Q) = ⟨k,q.val⟩
    rw [hg]
    exact congrArg (fun a : Quotient (J k).val => (⟨k,a⟩ : Q)) hq
  let Z : Finset Q := Finset.univ.biUnion fun k =>
    (forbidden k).image (fun a => (⟨k,a⟩ : Q))
  obtain ⟨g,hAvoid⟩ := AclOwners.finite_action_avoidance
    (G := stabilizer) moving Z (by
      intro q hq
      obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hq
      exact hOrbit k)
  let x : X i := (g : G) • x₀
  have hK : K x₀ x := K.val.symm (Quotient.exact g.property)
  have hx : x ∈ originalActualClassFibre S E c := by
    rw [original_actual_class_fibre_eq_full_meet_class S E c x₀ hx₀]
    exact hK
  refine ⟨x,hx,?_⟩
  intro k hk
  have hMoving : output k ∈ moving :=
    Finset.mem_image.mpr ⟨k,Finset.mem_univ k,rfl⟩
  have hForbidden : (⟨k,Quotient.mk (J k).val x⟩ : Q) ∈ Z :=
    Finset.mem_biUnion.mpr
      ⟨k,Finset.mem_univ k,Finset.mem_image.mpr ⟨_,hk,rfl⟩⟩
  exact hAvoid (output k) hMoving _ hForbidden rfl

/-- Terminal source C34: genuine original exact-ball Helly supplies the one
common real fibre, then the one-action theorem avoids all unforced lists.
The full NR2 and FULL cover assumptions retain their separate source roles. -/
theorem original_terminal_common_fibre_simultaneous_avoidance
    (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i : ι} (nr2 : SortNR2 S i)
    (hCover : OriginalAllFullCoversInfinite S (i := i))
    {m n : Nat} (E : Fin m → ColourEq S i) (c : Fin m → X i)
    (hPair : ∀ j k : Fin m,
      ∃ x : X i, E j (c j) x ∧ E k (c k) x)
    (J : Fin n → ColourEq S i)
    (hUnforced : ∀ k, ¬ originalActualMeetEquivalence S E ≤ J k)
    (forbidden : ∀ k, Finset (Quotient (J k).val)) :
    ∃ x : X i, x ∈ originalActualClassFibre S E c ∧
      ∀ k, Quotient.mk (J k).val x ∉ forbidden k := by
  obtain ⟨x₀,hx₀⟩ :=
    original_terminal_actual_pairwise_class_helly S H cco nr2 E c hPair
  exact original_actual_common_fibre_simultaneous_avoidance
    S H hCover E c x₀ hx₀ J hUnforced forbidden

end CCO.TypedOrbitFrames
