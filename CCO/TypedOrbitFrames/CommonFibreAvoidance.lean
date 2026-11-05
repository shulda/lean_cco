import CCO.TypedOrbitFrames.ActualPairwiseHelly
import CCO.TypedOrbitFrames.OriginalFibreMotion
import CCO.RawExact.CanonicalQuotients
import CCO.UnaryFreshFrames.Quotient.Avoidance

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
allowed. This is a source instance of the accepted CCO-free fibre theorem. -/
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
  let p : X i → Quotient K.val := Quotient.mk K.val
  let output : Fin n → (X i → Q) :=
    fun k x => ⟨k, Quotient.mk (J k).val x⟩
  let T : Set (X i → Q) := Set.range output
  have hp : UnaryFreshFrames.Quotient.Equivariant (G := G) p := by
    intro g x
    rfl
  have hT : ∀ f ∈ T, UnaryFreshFrames.Quotient.Equivariant (G := G) f := by
    rintro f ⟨k,rfl⟩ g x
    rfl
  have hfinite : ((fun f : X i → Q => f x₀) '' T).Finite :=
    (Set.finite_range output).image _
  have hInfinite (k : Fin n) :
      (UnaryFreshFrames.Quotient.FibreValues p (output k) (p x₀)).Infinite := by
    let C := {q : Quotient (J k).val //
      q ∈ originalJClassesWithinHClass S K (J k) x₀}
    letI : Infinite C :=
      original_unforced_J_classes_in_H_fibre_infinite
        S hCover K (J k) (hUnforced k) x₀
    let embed : C → Q := fun q => ⟨k,q.val⟩
    have hEmbed : Function.Injective embed := by
      intro q r h
      apply Subtype.ext
      simpa only [embed, Sigma.mk.injEq, heq_eq_eq, true_and] using h
    apply Set.infinite_of_injective_forall_mem hEmbed
    intro q
    obtain ⟨y,hy,hq⟩ := q.property
    refine ⟨y, ?_, ?_⟩
    · exact Quotient.sound (K.val.symm hy)
    · exact congrArg (fun a : Quotient (J k).val => (⟨k,a⟩ : Q)) hq
  let Z : Finset Q := Finset.univ.biUnion fun k =>
    (forbidden k).image (fun a => (⟨k,a⟩ : Q))
  obtain ⟨x,hpx,hAvoid⟩ :=
    UnaryFreshFrames.Quotient.common_fibre_avoidance
      (G := G) (S.original_sort_transitive_of_homogeneous H i)
      p hp T hT x₀ hfinite
      (by rintro f ⟨k,rfl⟩ _; exact hInfinite k) Z
  have hK : K x₀ x := K.val.symm (Quotient.exact hpx)
  have hx : x ∈ originalActualClassFibre S E c := by
    rw [original_actual_class_fibre_eq_full_meet_class S E c x₀ hx₀]
    exact hK
  refine ⟨x,hx,?_⟩
  intro k hk
  have hKernel : ¬ UnaryFreshFrames.Quotient.KernelLe p (output k) := by
    intro hle
    apply hUnforced k
    intro a b hab
    have htag := hle a b (Quotient.sound hab)
    have hq : Quotient.mk (J k).val a = Quotient.mk (J k).val b := by
      simpa only [output, Sigma.mk.injEq, heq_eq_eq, true_and] using htag
    exact Quotient.exact hq
  apply hAvoid (output k) ⟨k,rfl⟩ hKernel
  exact Finset.mem_biUnion.mpr
    ⟨k, Finset.mem_univ k, Finset.mem_image.mpr ⟨_,hk,rfl⟩⟩

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
