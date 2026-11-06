import CCO.HiddenSAPReadings.SourceSupport
import CCO.HiddenSAPReadings.OrbitalNamedTerms
import Mathlib.Data.Fin.VecNotation

/-!
# The real-identity exception is a bounded OLD source defect

The comparison requirement below is actual source syntax: a displayed
binary tuple, literal equality, or an evaluated named unary graph. Its
preservation is proved from the source homomorphism. No premise saying
that every completion collapses the roots is supplied by the caller.
The empty orbital alternative then forces that collapse, contradicting
the HE map on the stated irreducible CLOSED old support.
-/

universe u v w r z
namespace CCO.HiddenSAPReadings.IdentityDefect
open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames CCO.GroupActions
noncomputable section

/-- Evaluation uses only the actual displayed partial source functions,
with the same named typed term syntax as the completed target. -/
def SourceValue {L : Language.{u}} [Finite (L).Sorts] [Finite L.Func] [Finite L.Rel]
    {P : Type z} (C : CCO.UnarySupport.Structure (partialSignature L) P)
    {i j : (L).Sorts} (t : Term L i j) (x y : P) : Prop :=
  match t with
  | .id _ => y = x
  | .func F s => ∃ q, SourceValue C s x q ∧ y ∈ C.func F q

theorem source_value_sort {L : Language.{u}} [Finite (L).Sorts]
    [Finite L.Func] [Finite L.Rel] {P : Type z}
    (C : CCO.UnarySupport.Structure (partialSignature L) P)
    {i j : (L).Sorts} (t : Term L i j) {x y : P}
    (hx : C.sort x = i) (h : SourceValue C t x y) : C.sort y = j := by
  induction t generalizing y with
  | id => exact h ▸ hx
  | func F s ih =>
    obtain ⟨q,hq,hy⟩ := h
    exact (C.func_sorted F q y hy).2

theorem source_value_closed {L : Language.{u}} [Finite (L).Sorts]
    [Finite L.Func] [Finite L.Rel] {P : Type z}
    (C : CCO.UnarySupport.Structure (partialSignature L) P)
    {D : Set P} (hD : C.IsClosed D) {i j : (L).Sorts} (t : Term L i j)
    {x y : P} (hx : x ∈ D) (h : SourceValue C t x y) : y ∈ D := by
  induction t generalizing y with
  | id => exact h ▸ hx
  | func F s ih =>
    obtain ⟨q,hq,hy⟩ := h
    exact hD F q (ih hq) hy

/-- Two occurrences of the SAME old root live in its actual unary
closure. Such a comparison is local unary data, rather than a new
STRONG identity-labelled binary edge. -/
theorem same_root_values_in_singleton {L : Language.{u}} [Finite (L).Sorts]
    [Finite L.Func] [Finite L.Rel] {P : Type z}
    (C : CCO.UnarySupport.Structure (partialSignature L) P)
    {i j k : (L).Sorts} (t : Term L i j) (s : Term L i k) {x y z : P}
    (ht : SourceValue C t x y) (hs : SourceValue C s x z) :
    y ∈ C.closureAt x ∧ z ∈ C.closureAt x := by
  exact ⟨source_value_closed C (C.isClosed_closure {x}) t (C.mem_closureAt x) ht,
    source_value_closed C (C.isClosed_closure {x}) s (C.mem_closureAt x) hs⟩

/-- A genuine source term value maps to that exact actual target value. -/
theorem source_value_map {L : Language.{u}} [Finite (L).Sorts]
    [Finite L.Func] [Finite L.Rel] {P : Type z} {V : Type v}
    {C : CCO.UnarySupport.Structure (partialSignature L) P}
    {A : Structure L V} (f : CCO.UnarySupport.Structure.Hom C (partialTarget A))
    {i j : (L).Sorts} (t : Term L i j) {x y : P} (h : SourceValue C t x y) :
    f.point y = A.eval t (f.point x) := by
  classical
  induction t generalizing y with
  | id => exact congrArg f.point h
  | func F s ih =>
    obtain ⟨q,hq,hy⟩ := h
    have hm := f.map_func F q y hy
    dsimp only [partialTarget] at hm
    split at hm
    · have he : f.point y = A.func F (f.point q) := hm
      exact he.trans (congrArg (A.func F) (ih hq))
    · exact False.elim hm

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)
variable (hCover : ∀ i : ι, OriginalAllFullCoversInfinite S (i := i))

local notation "nr2" => CCO.HereditaryHiddenOrbits.terminalNR2 S hCover
local notation "L" => originalCompletedLanguage S H sap nr2
local notation "A" => originalCompletedStructure S H sap nr2
local notation "T" => originalPartialTarget S H sap nr2

/-- Exactly the three allowed comparison forms, with ACTUAL source
evidence at the two displayed old term values. -/
inductive DisplayedComparison {P : Type z}
    (C : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P) :
    (C D : (L).Sorts) → ((A).Carrier C → (A).Carrier D → Prop) → P → P → Prop where
  | binary {D E} (name : OriginalCompletedCylinderBinaryName S H) {x y : P}
      (h : C.rel name ![x,y]) :
      DisplayedComparison C D E (fun q r =>
        originalCompletedCylinderBinaryPredicate S H name q.val r.val) x y
  | equality (D) (x : P) : DisplayedComparison C D D (fun q r => q = r) x x
  | graph {D E} (t : Term L D E) {x y : P} (h : SourceValue C t x y) :
      DisplayedComparison C D E (fun q r => (A).typedEval t q = r) x y

theorem displayed_comparison_named {P : Type z}
    {C : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P}
    {D E : (L).Sorts} {Θ : (A).Carrier D → (A).Carrier E → Prop} {x y : P}
    (h : DisplayedComparison S H sap hCover C D E Θ x y) :
    NamedComparison S H sap nr2 D E Θ := by
  cases h with
  | binary name _ => exact .binary name
  | equality => exact .equality _
  | graph t _ => exact .graph t

theorem displayed_comparison_map {P : Type z}
    {C : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P}
    (f : CCO.UnarySupport.Structure.Hom C T)
    {D E : (L).Sorts} {Θ : (A).Carrier D → (A).Carrier E → Prop} {x y : P}
    (hx : C.sort x = D) (hy : C.sort y = E)
    (h : DisplayedComparison S H sap hCover C D E Θ x y) :
    Θ ⟨f.point x,(f.sort_eq x).trans hx⟩ ⟨f.point y,(f.sort_eq y).trans hy⟩ := by
  cases h with
  | binary name hr => exact f.map_rel name ![x,y] hr
  | equality => rfl
  | graph t ht =>
    apply Subtype.ext
    exact (source_value_map f t ht).symm

/-- Consume the exact orbital exception: every root pair in that
orbital is the SAME tagged original real point, even for different
output carriers. No STRONG identity atom is inserted. -/
theorem exception_root_eq {i j : ι} {Q : Type*} {R : Type*}
    [MulAction G Q] [MulAction G R]
    (τ : X i → Q) (σ : X j → R) (q : Q) (r : R)
    (h : RealIdentityException (X := X) (G := G) τ σ q r)
    {x : X i} {y : X j} (hxy : orbital (G := G) q r (τ x) (σ y)) :
    (⟨i,x⟩ : Sigma X) = ⟨j,y⟩ := by
  obtain ⟨hij,hτ,hσ,hGraph⟩ := h
  cases hij
  rw [hGraph] at hxy
  obtain ⟨p,hx,hy⟩ := hxy
  exact congrArg (Sigma.mk i) ((hτ.1 hx).trans (hσ.1 hy).symm)

/-- C44 source instance, including its OLD support bound. The named
terms, single comparison and its preservation are all discharged from
actual source data. Only the source's stated irreducibility and chosen
singleton bounds remain hypotheses, exactly as in source13 A07. -/
theorem bounded_named_identity_defect {P : Type z} [Finite P]
    (C : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
    (B : Finset P) {k m : ℕ} (hB : B.card ≤ k)
    (hm : ∀ b ∈ B, Nat.card (C.closureAt b) ≤ m)
    (hirr : (C.closureStructure (B : Set P)).Irreducible)
    {u v : P} (huD : u ∈ C.closure (B : Set P)) (hvD : v ∈ C.closure (B : Set P))
    (hne : u ≠ v) {i j : ι}
    (hu : C.sort u = ⟨⟨i,.inl ()⟩⟩) (hv : C.sort v = ⟨⟨j,.inl ()⟩⟩)
    {D E : (L).Sorts}
    (t : Term L ⟨⟨i,.inl ()⟩⟩ D) (s : Term L ⟨⟨j,.inl ()⟩⟩ E)
    (Θ : (A).Carrier D → (A).Carrier E → Prop) {w z : P}
    (ht : SourceValue C t u w) (hs : SourceValue C s v z)
    (hComp : DisplayedComparison S H sap hCover C D E Θ w z)
    (hEmpty : comparisonSpectrum S (namedRealTermMap S H sap nr2 t)
      (namedRealTermMap S H sap nr2 s) Θ = ∅) :
    Nat.card (C.closure (B : Set P)) ≤ k * m ∧
      ¬ ∃ f : CCO.UnarySupport.Structure.Hom C T, f.HomEmbedding := by
  refine ⟨SourceSupport.generated_support_card C B hB hm,?_⟩
  rintro ⟨f,hf⟩
  have hfu : (A).sort (f.point u) = ⟨⟨i,.inl ()⟩⟩ := (f.sort_eq u).trans hu
  have hfv : (A).sort (f.point v) = ⟨⟨j,.inl ()⟩⟩ := (f.sort_eq v).trans hv
  obtain ⟨x,hx⟩ := original_completed_real_carrier_exists S H sap nr2 ⟨f.point u,hfu⟩
  obtain ⟨y,hy⟩ := original_completed_real_carrier_exists S H sap nr2 ⟨f.point v,hfv⟩
  have htw := source_value_map f t ht
  have hsz := source_value_map f s hs
  change f.point u = Sum.inl ⟨i,x⟩ at hx
  change f.point v = Sum.inl ⟨j,y⟩ at hy
  have hOut := displayed_comparison_map S H sap hCover f
    (source_value_sort C t hu ht) (source_value_sort C s hv hs) hComp
  have hw : f.point w = (namedRealTermMap S H sap nr2 t x).val := by
    rw [htw,hx]
    rfl
  have hz : f.point z = (namedRealTermMap S H sap nr2 s y).val := by
    rw [hsz,hy]
    rfl
  have hWitness : Θ (namedRealTermMap S H sap nr2 t x)
      (namedRealTermMap S H sap nr2 s y) := by
    have hqw : (⟨f.point w,(f.sort_eq w).trans (source_value_sort C t hu ht)⟩ : (A).Carrier D) =
        namedRealTermMap S H sap nr2 t x := Subtype.ext hw
    have hrz : (⟨f.point z,(f.sort_eq z).trans (source_value_sort C s hv hs)⟩ : (A).Carrier E) =
        namedRealTermMap S H sap nr2 s y := Subtype.ext hz
    rwa [hqw,hrz] at hOut
  letI : MulAction G ((A).Carrier D) := completedSortAction S H sap nr2 D
  letI : MulAction G ((A).Carrier E) := completedSortAction S H sap nr2 E
  have hOrb := named_comparison_is_one_orbital S H sap nr2
    (displayed_comparison_named S H sap hCover hComp) _ _ hWitness
  have hPalette : orbitalPalette (G := G) S (namedRealTermMap S H sap nr2 t)
      (namedRealTermMap S H sap nr2 s)
      (namedRealTermMap S H sap nr2 t x) (namedRealTermMap S H sap nr2 s y) = ∅ := by
    rw [← comparisonSpectrum_orbital S H _ _
      (namedRealTermMap_equivariant S H sap nr2 t)
      (namedRealTermMap_equivariant S H sap nr2 s),← hOrb]
    exact hEmpty
  have hException := (orbitalPalette_empty_iff S H _ _
    (namedRealTermMap_surjective S H sap nr2 t)
    (namedRealTermMap_surjective S H sap nr2 s)
    (namedRealTermMap_equivariant S H sap nr2 t)
    (namedRealTermMap_equivariant S H sap nr2 s) _ _).mp hPalette
  have hRoots := exception_root_eq _ _ _ _ hException
    (orbital_nonempty (namedRealTermMap S H sap nr2 t x)
      (namedRealTermMap S H sap nr2 s y))
  have hCollapse : f.point u = f.point v := hx.trans
    ((congrArg (fun p : Sigma X => (Sum.inl p : OriginalCompletedNamedCarrier S H)) hRoots).trans hy.symm)
  exact hne ((hf _ (C.isClosed_closure _) hirr).1 huD hvD hCollapse)

end
end CCO.HiddenSAPReadings.IdentityDefect
