import CCO.Atomic
import CCO.GroupActions

/-!
# Actual atomic supports and pair orbitals

`PairHomogeneity` below is an *explicit* property of an actual group
action, not a new axiom and not a theorem of CCO or SAP.  The planned
source-level proof must derive it from finite induced homogeneity.
The results here already establish the exact, equality-inclusive
representation conversion assuming this property.
-/

universe u v w

namespace CCO.AtomicSource

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource ι X)
variable {i j : ι}
variable {G : Type*} [Group G]
variable [MulAction G (X i)] [MulAction G (X j)]

/-- Pair-colour preservation by an actual diagonal group action. -/
def ColourInvariant : Prop :=
  ∀ (g : G) (x : X i) (y : X j),
    S.colour (g • x) (g • y) = S.colour x y

/-- Complete one- and two-point homogeneity on these named original sorts. -/
def PairHomogeneous : Prop :=
  ∀ (x x' : X i) (y y' : X j),
    S.colour x y = S.colour x' y' →
      ∃ g : G, g • x = x' ∧ g • y = y'

/-- RAW support contains the optional true diagonal, not just diversity
atoms. The output is tagged by the ordered source/target sort pair. -/
def rawSupport (R : TRel X i j) : Set (Option (S.Atom i j)) :=
  { c | ∃ x y, R x y ∧ S.colour x y = c }

def representedSupport (A : Set (Option (S.Atom i j))) : TRel X i j :=
  fun x y => S.colour x y ∈ A

theorem rawSupport_represents_invariant (R : TRel X i j)
    (hInv : TRel.Invariant (G := G) R)
    (hPair : S.PairHomogeneous (G := G) (i := i) (j := j)) :
    S.representedSupport (S.rawSupport R) = R := by
  funext x y
  apply propext
  constructor
  · rintro ⟨a, b, hab, hcol⟩
    obtain ⟨g, hgx, hgy⟩ := hPair a x b y hcol
    have hg := hInv g a b hab
    simpa only [hgx, hgy] using hg
  · intro hxy
    exact ⟨x, y, hxy, rfl⟩

/-- The actual ordered-pair orbit of each (realized) named diversity
atom is exactly that atom's represented binary relation. -/
theorem atom_is_actual_orbital (a : S.Atom i j)
    (hInv : S.ColourInvariant (G := G) (i := i) (j := j))
    (hPair : S.PairHomogeneous (G := G) (i := i) (j := j)) :
    ∃ x₀ : X i, ∃ y₀ : X j,
      S.atomRel a x₀ y₀ ∧
      S.atomRel a = GroupActions.orbital (G := G) x₀ y₀ := by
  obtain ⟨x₀, y₀, h₀⟩ := S.realized a
  refine ⟨x₀, y₀, h₀, ?_⟩
  funext x y
  apply propext
  constructor
  · intro hxy
    obtain ⟨g, hgx, hgy⟩ := hPair x₀ x y₀ y (h₀.trans hxy.symm)
    exact ⟨g, hgx, hgy⟩
  · rintro ⟨g, rfl, rfl⟩
    change S.colour (g • x₀) (g • y₀) = some a
    rw [hInv]
    exact h₀

/-- A represented invariant relation consists precisely of the
optional named atomic colours it realizes. -/
theorem invariant_iff_union_of_colours (R : TRel X i j)
    (hPair : S.PairHomogeneous (G := G) (i := i) (j := j)) :
    TRel.Invariant (G := G) R →
      R = (fun x y => ∃ c : Option (S.Atom i j),
          c ∈ S.rawSupport R ∧ S.colour x y = c) := by
  intro hInv
  calc
    R = S.representedSupport (S.rawSupport R) :=
      (S.rawSupport_represents_invariant R hInv hPair).symm
    _ = (fun x y => ∃ c : Option (S.Atom i j),
          c ∈ S.rawSupport R ∧ S.colour x y = c) := by
      funext x y
      apply propext
      constructor
      · intro h
        exact ⟨S.colour x y, h, rfl⟩
      · rintro ⟨c, hc, hcol⟩
        change S.colour x y ∈ S.rawSupport R
        rw [hcol]
        exact hc

end CCO.AtomicSource
