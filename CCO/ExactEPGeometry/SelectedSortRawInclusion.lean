import CCO.ExactEPGeometry.SelectedSortSource
import CCO.RigidGroupoid.Geometry.Basic

/-!
# Exact RAW inclusion from genuinely selected sorts into the full source

Every intermediate sort of a selected-source word is already a selected
sort, so its literal inclusion has exactly the same real middle witnesses
in the original source. This direction needs no equivariant carrier map.
It does not assert the opposite restriction of arbitrary old words, whose
middle sorts might have been deleted. Logical identity and empty finite
exact lists are both retained.
-/

universe u v w
namespace CCO.ExactEPGeometry

open RigidGroupoid.Geometry

noncomputable section

variable {ι κ : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable [Fintype κ] (σ : κ ↪ ι)

/-- Include every RAW letter and every intermediate selected sort
literally into the original full language. -/
def selectedSortRawInclusion {i j : κ} :
    RawWord (selectedSortAtomicSource S σ) i j → RawWord S (σ i) (σ j)
  | .nil i => .nil (σ i)
  | .identity tail => .identity (selectedSortRawInclusion tail)
  | .atom a tail => .atom a (selectedSortRawInclusion tail)

/-- Exact equality of whole word relations, with the same real witnesses. -/
theorem selectedSortRawInclusion_iff {i j : κ}
    (word : RawWord (selectedSortAtomicSource S σ) i j)
    (x : X (σ i)) (y : X (σ j)) :
    RawWord.relation (selectedSortAtomicSource S σ) word x y ↔
      RawWord.relation S (selectedSortRawInclusion S σ word) x y := by
  induction word with
  | nil i => exact Iff.rfl
  | identity tail ih => exact ih x y
  | @atom i j k a tail ih =>
    change (∃ z : X (σ j), S.atomRel a x z ∧
      RawWord.relation (selectedSortAtomicSource S σ) tail z y) ↔
      ∃ z : X (σ j), S.atomRel a x z ∧
        RawWord.relation S (selectedSortRawInclusion S σ tail) z y
    exact exists_congr (fun z => and_congr Iff.rfl (ih z y))

/-- Include the complete finite exact presentation and its actual
nonempty witness; no mathematical exactness provider is introduced. -/
def selectedSortExactInclusion {i j : κ}
    (W : RawExact.NonemptyExact (selectedSortAtomicSource S σ) i j) :
    RawExact.NonemptyExact S (σ i) (σ j) := by
  refine ⟨W.words.map (selectedSortRawInclusion S σ),?_⟩
  obtain ⟨x,y,hxy⟩ := W.nonempty
  refine ⟨x,y,?_⟩
  intro word hw
  obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hw
  exact (selectedSortRawInclusion_iff S σ old x y).mp (hxy old hold)

theorem selectedSortExactInclusion_iff {i j : κ}
    (W : RawExact.NonemptyExact (selectedSortAtomicSource S σ) i j)
    (x : X (σ i)) (y : X (σ j)) :
    RawExact.evaluate (selectedSortAtomicSource S σ) W.words x y ↔
      RawExact.evaluate S (selectedSortExactInclusion S σ W).words x y := by
  constructor
  · intro h word hw
    obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hw
    exact (selectedSortRawInclusion_iff S σ old x y).mp (h old hold)
  · intro h word hw
    apply (selectedSortRawInclusion_iff S σ word x y).mpr
    exact h _ (List.mem_map.mpr ⟨word,hw,rfl⟩)

/-- Any actual selected-source full RAW-exact relation is genuinely full
RAW exact at its same endpoint carriers in the original full language. -/
theorem selectedSortFullExact_inclusion {i j : κ}
    (R : TRel (fun k => X (σ k)) i j)
    (hR : FullExact (selectedSortAtomicSource S σ) R) : FullExact S R := by
  obtain ⟨W,hW⟩ := hR
  refine ⟨selectedSortExactInclusion S σ W,?_⟩
  funext x y
  apply propext
  exact (selectedSortExactInclusion_iff S σ W x y).symm.trans
    (Iff.of_eq (congrFun (congrFun hW x) y))

end
end CCO.ExactEPGeometry
