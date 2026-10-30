import CCO.ParityHasse.Original.SourceHasse

/-! Full invariant-lattice cover and finite-index source exports. These
retain the genuinely SAP-free accepted theorem and arbitrary endpoints. -/
universe u v w t
namespace CCO.OrbitalCover
open ParityHasse.Original
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) {i : ι}
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

/-- C07/C10: a cover in the FULL invariant lattice, with no exactness or
SAP assumptions, has index two whenever its index is finite. -/
theorem finite_cover_two (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,0,w} S)
    (E F : ColourEq S i) (cover : E ⋖ F) (a : X i)
    [Finite (RelativeClass E.val F.val a)] :
    relativeIndex E.val F.val a = 2 :=
  full_relative_hasse S H cco E F cover a

/-- C08/C09: the finite full invariant lattice's saturated-chain/index
multiplication proof, including equality at index one. -/
theorem finite_index_power_two (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,0,w} S)
    (E F : ColourEq S i) (leEF : E ≤ F) (a : X i)
    [Finite (RelativeClass E.val F.val a)] :
    ∃ n : Nat, relativeIndex E.val F.val a = 2^n :=
  finite_relative_power_two S H cco E F leEF a

end CCO.OrbitalCover
