import CCO.RealHull.Geometry.OnePoint
import Mathlib.Data.Set.Finite.Range

/-! Actual finite anchors with independent formal index universes. -/
universe v w t z
namespace CCO.RealHull.Geometry
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M]

theorem triangle_over_pair (H : HomogeneousSource S G) {a b c : Atom S}
    (htri : S.Triangle a b c) {x z : M} (hc : col S x z = some c) :
    ∃ y, col S x y = some a ∧ col S y z = some b := by
  have hm : col S x z ∈ prod S {some a} {some b} :=
    hc.symm ▸ (mem_row S a b c).mpr htri
  obtain ⟨y,hy,hz⟩ := (prod_at_pair S H _ _ x z).mp hm
  exact ⟨y,Set.mem_singleton_iff.mp hy,Set.mem_singleton_iff.mp hz⟩

theorem onePointExtension_indexed (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) {B : Type z} [Finite B]
    (e : B ↪ M) (q : B → Atom S)
    (htri : ∀ a b : B, a ≠ b → ∀ c : Atom S,
      col S (e a) (e b) = some c → S.Triangle (q a) c (q b)) :
    ∃ y : M, (∀ b, y ≠ e b) ∧ ∀ b, col S y (e b) = some (q b) := by
  classical
  let A : Finset M := (Set.finite_range (fun b : B => e b)).toFinset
  have hindex (a : ↥A) : ∃ b, e b = a.val := by
    have ha : a.val ∈ Set.range (fun b : B => e b) := by
      simpa only [A,Set.Finite.mem_toFinset] using a.property
    exact ha
  let idx : ↥A → B := fun a => Classical.choose (hindex a)
  have hidx (a : ↥A) : e (idx a) = a.val := Classical.choose_spec (hindex a)
  let qA : ↥A → Atom S := fun a => q (idx a)
  have htriA : ∀ a b : ↥A, a ≠ b → ∀ c : Atom S,
      col S a.val b.val = some c → S.Triangle (qA a) c (qA b) := by
    intro a b hab c hc
    apply htri (idx a) (idx b)
    · intro he
      apply hab
      exact Subtype.ext ((hidx a).symm.trans ((congrArg e he).trans (hidx b)))
    · simpa only [hidx a,hidx b] using hc
  obtain ⟨y,hy,hq⟩ := onePointExtension S H cco A qA htriA
  have heA (b : B) : e b ∈ A := by
    simpa only [A,Set.Finite.mem_toFinset] using
      (show e b ∈ Set.range (fun t : B => e t) from ⟨b,rfl⟩)
  have hidxe (b : B) : idx ⟨e b,heA b⟩ = b := e.injective (hidx _)
  refine ⟨y,?_,?_⟩
  · intro b he
    exact hy (he ▸ heA b)
  · intro b
    have hh := hq ⟨e b,heA b⟩
    simpa only [qA,hidxe] using hh

end CCO.RealHull.Geometry
