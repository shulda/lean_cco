import CCO.RankInduction.Basis

/-! Actual orbital palettes and full-automorphism closed-span adapters.
These are finite-homogeneity transfers, with no global quotient section. -/

universe v w t
namespace CCO.RankInduction
open RawExact Owners.Product Owners.Provider

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)

def namedPalette (r : M → M → Prop) : Set (S.Atom () ()) :=
  {a | ∀ x y, S.colour (i := ()) (j := ()) x y = some a → r x y}

include H

theorem menuRel_namedPalette (r : M → M → Prop) (diagonal : ∀ x, ¬ r x x)
    (invariant : ∀ (g : G) x y, r x y → r (g • x) (g • y)) :
    S.menuRel (namedPalette S r) = r := by
  funext x y
  apply propext
  constructor
  · rintro ⟨a,ha,hxy⟩
    exact ha x y hxy
  · intro hr
    have hne : x ≠ y := by rintro rfl; exact diagonal x hr
    cases hc : S.colour (i := ()) (j := ()) x y with
    | none =>
      exact False.elim (hne (eq_of_heq (Sigma.mk.inj ((S.colour_none_iff x y).mp hc)).2))
    | some a =>
      refine ⟨a,?_,hc⟩
      intro x' y' hc'
      obtain ⟨g,hgx,hgy⟩ := S.pair_homogeneous_of_homogeneous H x x' y y' (hc.trans hc'.symm)
      exact hgx ▸ hgy ▸ invariant g x y hr

theorem strong_closed_from_full (r : M → M → Prop)
    (hs : FiniteLift.StrongClosedAmalgamation (FiniteLift.FullAut G M)
      (FiniteLift.aclSet (FiniteLift.FullAut G M)) r) :
    FiniteLift.StrongClosedAmalgamation G (FiniteLift.aclSet G) r := by
  intro C L R finiteC finiteL finiteR closedC closedL closedR f g
  let f' : FiniteLift.OrbitalEmbedding (FiniteLift.FullAut G M) C L := {
    toEmbedding := f.toEmbedding
    pair := fun x y => (FiniteLift.full_orbital_iff _ _ _ _).mpr (f.pair x y) }
  let g' : FiniteLift.OrbitalEmbedding (FiniteLift.FullAut G M) C R := {
    toEmbedding := g.toEmbedding
    pair := fun x y => (FiniteLift.full_orbital_iff _ _ _ _).mpr (g.pair x y) }
  obtain ⟨W,finiteW,l,r',commute,strong,cross⟩ := hs C L R finiteC finiteL finiteR
    ((FiniteLift.aclSet_full_eq S H C finiteC).trans closedC)
    ((FiniteLift.aclSet_full_eq S H L finiteL).trans closedL)
    ((FiniteLift.aclSet_full_eq S H R finiteR).trans closedR) f' g'
  refine ⟨W,finiteW,⟨l.toEmbedding,?_⟩,⟨r'.toEmbedding,?_⟩,commute,strong,cross⟩
  · intro x y
    exact (FiniteLift.full_orbital_iff _ _ _ _).mp (l.pair x y)
  · intro x y
    exact (FiniteLift.full_orbital_iff _ _ _ _).mp (r'.pair x y)

end CCO.RankInduction
