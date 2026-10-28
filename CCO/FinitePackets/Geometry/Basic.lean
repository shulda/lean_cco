import CCO.ParityHasse.Original.RelativeIndices
import CCO.ParityHasse.Original.Transposition
import CCO.RealHull.Geometry.RamseySource
import CCO.RealHull.Geometry.Supports

/-! Actual full invariant equivalences and guarded finite relative indices.
The accepted lattice is modular; no distributive or exact sublattice is used. -/
universe u v w t
namespace CCO.FinitePackets.Geometry
open CCO.ParityHasse.Original CCO.RealHull.Geometry
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) {i : ι}

/-- Finiteness of the ACTUAL classes inside every upper class.  Order of the
endpoints is a separate hypothesis, rather than hidden in this predicate. -/
def FiniteIndex (J K : ColourEq S i) : Prop :=
  ∀ x : X i, Finite (RelativeClass J.val K.val x)

theorem finiteIndex_self (J : ColourEq S i) : FiniteIndex S J J := by
  intro x
  have hs : Subsingleton (RelativeClass J.val J.val x) := by
    constructor
    intro p q
    refine Quotient.inductionOn₂ p q ?_
    intro a b
    exact Quotient.sound (J.val.trans (J.val.symm a.property) b.property)
  letI := hs
  exact Finite.of_subsingleton

theorem finiteIndex_lower {J K L : ColourEq S i}
    (hKL : K ≤ L) (h : FiniteIndex S J L) : FiniteIndex S J K := by
  intro x
  letI := h x
  exact finite_relative_left J.val K.val L.val hKL x

theorem finiteIndex_upper {J K L : ColourEq S i}
    (hJK : J ≤ K) (h : FiniteIndex S J L) : FiniteIndex S K L := by
  intro x
  letI := h x
  exact finite_relative_right J.val K.val L.val hJK x

variable {G : Type t} [Group G] [∀ j, MulAction G (X j)]

/-- One actual class is enough by the accepted real automorphism motion. -/
theorem finiteIndex_iff_at (H : HomogeneousSource S G) (J K : ColourEq S i) (x : X i) :
    FiniteIndex S J K ↔ Finite (RelativeClass J.val K.val x) := by
  refine ⟨fun h => h x, ?_⟩
  intro h y
  letI := h
  exact Finite.of_equiv _ (uniformRelativeClassEquiv S H J K x y)

section SingleSort
variable {M : Type v} (T : AtomicSource.{0,v,w} Unit (fun _ => M))

/-- Inclusion of one actual old diversity orbital, including all its pairs. -/
def AtomBelow (E : ColourEq T ()) (a : Atom T) : Prop :=
  ∀ x y : M, col T x y = some a → E x y

theorem atomBelow_iff_mem (E : ColourEq T ()) (a : Atom T) :
    AtomBelow T E a ↔ a ∈ diversitySupport T E := by
  obtain ⟨x,y,hxy⟩ := colour_realized T (some a)
  exact ⟨fun h => ⟨x,y,h x y hxy,hxy⟩,
    fun h u v huv => (mem_diversitySupport T E huv).mp h⟩

theorem atomBelow_mono {E F : ColourEq T ()} (hEF : E ≤ F)
    {a : Atom T} (ha : AtomBelow T E a) : AtomBelow T F a :=
  fun x y hxy => hEF (ha x y hxy)

end SingleSort
end CCO.FinitePackets.Geometry
