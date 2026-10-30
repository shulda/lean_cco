import CCO.APCharacter.Masks
import CCO.RawExact.Convolution
import CCO.RawSource

/-! Locally allowed actual typed paths have allowed OLD endpoint outputs.
No realization of the marked age is assumed. Original homogeneity propagates
a selected intermediate atom over its entire old orbital. -/
universe u v w t
namespace CCO.APCharacter
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
namespace MaskData
variable (M : MaskData S)

inductive MarkedWord : {i j : ι} → Bit → Bit → Type (max u w) where
  | nil (i : ι) (ε : Bit) (valid : M.validBit i ε) : MarkedWord (i := i) (j := i) ε ε
  | atom {i j k : ι} {ε η θ : Bit} (a : S.Atom i j)
      (valid : M.validBit i ε) (allowed : M.allowed (some a) ε η)
      (tail : MarkedWord (i := j) (j := k) η θ) : MarkedWord (i := i) (j := k) ε θ

namespace MarkedWord
variable {M} {i j : ι} {ε η : Bit}
def word {i j : ι} {ε η : Bit} : M.MarkedWord (i := i) (j := j) ε η → RawWord S i j
  | .nil i _ _ => .nil i
  | .atom a _ _ tail => .atom a tail.word

theorem valid_start (p : M.MarkedWord (i := i) (j := j) ε η) : M.validBit i ε := by
  cases p with
  | nil _ _ h => exact h
  | atom _ h _ _ => exact h

theorem valid_end (p : M.MarkedWord (i := i) (j := j) ε η) : M.validBit j η := by
  induction p with
  | nil _ _ h => exact h
  | atom _ _ _ _ ih => exact ih

variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (laws : M.Calculus)

include H laws in
theorem allowed_output (p : M.MarkedWord (i := i) (j := j) ε η) :
    ∃ x y, RawWord.relation S p.word x y ∧ M.allowed (S.colour x y) ε η := by
  induction p with
  | nil i ε h =>
    let x : X i := Classical.choice (S.nonemptySort i)
    refine ⟨x,x,rfl,?_⟩
    have hc : S.colour x x = none := (S.colour_none_iff x x).mpr rfl
    rw [hc]
    exact (M.identity i ε ε).mpr ⟨rfl,h⟩
  | @atom i j k ε η θ a hv ha tail ih =>
    obtain ⟨y,z,hyz,hc⟩ := ih
    obtain ⟨xa,ya,haa⟩ := S.realized a
    obtain ⟨x,z',⟨y',hxy',hy'z'⟩,hallowed⟩ := laws.totality (some a) (S.colour y z)
      ε η θ hv tail.valid_start tail.valid_end ha hc ⟨xa,ya,haa⟩ ⟨y,z,rfl⟩
    have hTail : RawWord.relation S tail.word y' z' := by
      obtain ⟨g,hgy,hgz⟩ := (S.pair_homogeneous_of_homogeneous H) y y' z z' hy'z'.symm
      simpa only [hgy,hgz] using (RawExact.word_invariant_of_homogeneous S H tail.word) g y z hyz
    exact ⟨x,z',⟨y',hxy',hTail⟩,hallowed⟩

end MarkedWord
end MaskData
end CCO.APCharacter
