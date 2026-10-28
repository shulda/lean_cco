import CCO.RealHull.Geometry.FibreSource
import CCO.RealHull.Geometry.Localisation

/-! Any finite set of distinct prescribed spoke colours is a literal realised
star. Its anchor is actual, complete, and contains exactly one point per row.
No source SAP or independent artificial realisability premise is required. -/
universe v w t
namespace CCO.RealHull.Canonical
open Geometry
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable [DecidableEq M]

structure RealisedStar (P : Finset (Atom S)) where
  anchor : Finset M
  spoke : ↥anchor → Atom S
  centre : FibreSet S anchor spoke
  range_spoke : Set.range spoke = (↑P : Set (Atom S))

variable {G : Type t} [Group G] [MulAction G M]

noncomputable def starOfFinset (H : HomogeneousSource S G) (P : Finset (Atom S)) :
    RealisedStar S P := by
  classical
  let x : M := Classical.choice (S.nonemptySort ())
  have hpoint : ∀ p : ↥P, ∃ y : M, col S x y = some p.val :=
    fun p => colour_serial S H (some p.val) x
  choose f hf using hpoint
  have hfinj : Function.Injective f := by
    intro p q he
    apply Subtype.ext
    exact Option.some.inj ((hf p).symm.trans ((congrArg (col S x) he).trans (hf q)))
  let A : Finset M := Finset.univ.image f
  have hindex (a : ↥A) : ∃ p : ↥P, f p = a.val := by
    obtain ⟨p,_,hp⟩ := Finset.mem_image.mp a.property
    exact ⟨p,hp⟩
  let index : ↥A → ↥P := fun a => (hindex a).choose
  have hi (a : ↥A) : f (index a) = a.val := (hindex a).choose_spec
  let q : ↥A → Atom S := fun a => (index a).val
  refine ⟨A,q,⟨x,fun a => ?_⟩,?_⟩
  · exact (congrArg (col S x) (hi a).symm).trans (hf (index a))
  · ext p
    constructor
    · rintro ⟨a,rfl⟩
      exact (index a).property
    · intro hp
      let pp : ↥P := ⟨p,hp⟩
      let a : ↥A := ⟨f pp,Finset.mem_image.mpr ⟨pp,Finset.mem_univ _,rfl⟩⟩
      refine ⟨a,?_⟩
      exact congrArg Subtype.val (hfinj (hi a))

theorem RealisedStar.palette_eq {P : Finset (Atom S)} (star : RealisedStar S P) :
    {c : Atom S | ∀ a : ↥star.anchor, c ∈ square S (star.spoke a)} = squareMeet S P := by
  ext c
  constructor
  · intro hc p hp
    have hp' : p ∈ Set.range star.spoke := by rw [star.range_spoke]; exact hp
    obtain ⟨a,ha⟩ := hp'
    exact ha ▸ hc a
  · intro hc a
    have hp : star.spoke a ∈ P := by
      change star.spoke a ∈ (↑P : Set (Atom S))
      rw [← star.range_spoke]
      exact Set.mem_range_self a
    exact hc (star.spoke a) hp
end CCO.RealHull.Canonical
