import CCO.TypedOrbitFrames.FullCoverInfinite
import CCO.RealClosure.Bounds.TerminalNR2

/-! The literal standing FULL infinite-cover hypothesis discharges the
FULL original NR2 provider. The two-class decomposition is a genuine
finite quotient of an actual original class, not a named sublattice.
No extra terminal premise is requested by the source-facing exports. -/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Original CCO.RealClosure.Bounds

universe u v w r
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- A literal two-class original interval has finitely many actual lower
classes inside each upper class. This uses its full two-class cover. -/
theorem original_relative_index_two_finite
    {i : ι} (E F : Setoid (X i)) (hTwo : Selectors.RelativeIndexTwo E F)
    (x : X i) : Finite (RelativeClass E F x) := by
  classical
  obtain ⟨y,hy,_,hCover⟩ := hTwo.2 x
  let q₀ : RelativeClass E F x := Quotient.mk _ ⟨x,F.refl x⟩
  let q₁ : RelativeClass E F x := Quotient.mk _ ⟨y,hy⟩
  let f : Bool → RelativeClass E F x := fun b => if b then q₁ else q₀
  apply Finite.of_surjective f
  intro q
  refine Quotient.inductionOn q ?_
  intro z
  rcases (hCover z.val).mp z.property with hz | hz
  · refine ⟨false,?_⟩
    change q₀ = Quotient.mk _ z
    exact Quotient.sound hz
  · refine ⟨true,?_⟩
    change q₁ = Quotient.mk _ z
    exact Quotient.sound hz

/-- The standing A04 hypothesis on EVERY original sort implies the
existing FULL original NR2 predicate. No NR2 assumption is added. -/
theorem original_nr2_of_all_full_covers_infinite
    (hCover : ∀ i : ι, OriginalAllFullCoversInfinite S (i := i)) :
    Selectors.OriginalNR2 S := by
  intro i R T hR hT hTwo
  let E : ColourEq S i := ⟨R,hR⟩
  let F : ColourEq S i := ⟨T,hT⟩
  obtain ⟨x⟩ := S.nonemptySort i
  obtain ⟨y,hy,hne,_⟩ := hTwo.2 x
  have hEF : E < F := by
    refine lt_of_le_of_ne hTwo.1 ?_
    intro he
    apply hne
    have heq : R = T := congrArg Subtype.val he
    rw [heq]
    exact hy
  let : Finite (RelativeClass R T x) := original_relative_index_two_finite R T hTwo x
  let : Infinite (RelativeClass R T x) :=
    original_all_strict_full_indices_infinite S (hCover i) E F hEF x
  exact not_finite (RelativeClass R T x)

/-- Sortwise numerical NR2 is likewise a discharged standing provider. -/
theorem original_sort_nr2_of_all_full_covers_infinite
    {G : Type r} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G)
    (hCover : ∀ i : ι, OriginalAllFullCoversInfinite S (i := i)) (i : ι) :
    SortNR2 S i :=
  sortNR2_of_originalNR2 S H (original_nr2_of_all_full_covers_infinite S hCover)

end CCO.TypedOrbitFrames
