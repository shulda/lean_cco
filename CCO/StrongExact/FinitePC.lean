import CCO.StrongExact.PCNetwork
import Mathlib.Order.OrderIsoNat

/-!
# C10: finite termination and greatest STRONG PC fixed point

The domain of each ordered distinct formal pair is a subset of an
actual *finite* diversity palette. Thus the whole typed network space
is finite. A monotone deflationary synchronous update therefore
stabilizes, with no hypothesis that all domains remain nonempty.
The stationary network is the greatest stable refinement of the
original specified singleton/top network.
-/

universe u v w z

namespace CCO.StrongPC

variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u, v, w} ι X} {V : Type z}
variable (D : PartialDiagram S V)

/-- The off-diagonal pair type is finite because the formal vertex
set is finite. A pair's inequality witness is proof-irrelevant. -/
theorem finite_distinctPair (D : PartialDiagram S V) : Finite (DistinctPair V) := by
  letI : Finite V := D.finite_type
  let emb : DistinctPair V → V × V := fun p => (p.src, p.dst)
  have hi : Function.Injective emb := by
    intro p q h
    cases p with
    | mk x y hxy =>
      cases q with
      | mk x' y' hxy' =>
        have hparts := Prod.mk.inj h
        rcases hparts with ⟨hxx, hyy⟩
        cases hxx
        cases hyy
        rfl
  exact Finite.of_injective emb hi

/-- The full dependent space of typed Boolean pair menus is finite;
the proof uses B001's *actual* finite atom palettes, not a finite
approximation to the original source. -/
theorem finite_network : Finite (Network D) := by
  classical
  letI : Finite (DistinctPair V) := finite_distinctPair D
  haveI (p : DistinctPair V) :
      Fintype (S.Atom (D.vertexSort p.src) (D.vertexSort p.dst)) :=
    S.finiteAtom _ _
  haveI (p : DistinctPair V) :
      Finite (S.Menu (D.vertexSort p.src) (D.vertexSort p.dst)) := by
    infer_instance
  infer_instance

/-- A finite descending chain of Boolean networks eventually reaches
a genuine fixed point, not just a Post-fixed refinement. -/
theorem iterate_stabilizes (N : Network D) :
    ∃ n : Nat, Stable D (iterate D N n) := by
  classical
  letI : Finite (Network D) := finite_network D
  have hAnti : Antitone (iterate D N) := by
    apply antitone_nat_of_succ_le
    intro n
    exact iterate_succ_refines D N n
  obtain ⟨n, hconst⟩ := WellFoundedLT.antitone_chain_condition hAnti
  refine ⟨n, ?_⟩
  intro p
  have heq : iterate D N (n + 1) = iterate D N n :=
    (hconst (n + 1) (Nat.le_succ n)).symm
  exact congrArg (fun M : Network D => M p) heq

/-- An actual finite PC limit, defined by selecting one verified
stabilization index. Its value is independent of the chosen index. -/
noncomputable def fixedIndex : Nat :=
  Classical.choose (iterate_stabilizes D (initial D))

noncomputable def fixedNetwork : Network D :=
  iterate D (initial D) (fixedIndex D)

theorem fixedNetwork_stable : Stable D (fixedNetwork D) :=
  Classical.choose_spec (iterate_stabilizes D (initial D))

/-- Greatest fixed point of STRONG PC pruning inside the initial network.
The statement allows empty domains and arbitrary repeated sort names. -/
theorem fixedNetwork_greatest (M : Network D)
    (hStable : Stable D M)
    (hInside : Refines D M (initial D)) :
    Refines D M (fixedNetwork D) :=
  stable_refines_iterate D M (initial D)
    hStable hInside (fixedIndex D)


/-- Every actual injective completion supplies a survivor in the
canonical finite PC fixed point; this uses the same literal old fine
colour on each off-diagonal pair at every stage. -/
theorem fixedNetwork_supports_completion (f : DiagramHom D)
    (hf : f.IsInjective) :
    SupportsCompletion D (fixedNetwork D) f :=
  supports_all_iterates D f hf (fixedIndex D)

/-- In particular, the stable Boolean network never develops an empty
domain if the displayed diagram already has an injective completion. -/
theorem fixedNetwork_nonempty_of_completion (f : DiagramHom D)
    (hf : f.IsInjective) (p : DistinctPair V) :
    (fixedNetwork D p).Nonempty := by
  have hne : f.image p.src ≠ f.image p.dst :=
    fun he => p.ne (hf he)
  obtain ⟨a, ha⟩ :=
    S.some_colour_of_ne (f.point p.src) (f.point p.dst) hne
  exact ⟨a, fixedNetwork_supports_completion D f hf p a ha⟩

end CCO.StrongPC
