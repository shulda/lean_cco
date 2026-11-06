import CCO.TypedOrbitFrames.OrbitDiagram
import CCO.StrongExact.CycleCompletion

/-!
# Source11 T02: nonempty common STRONG spoke intersection

Two initially coincident formal copies of the realised complete old
one-point type are separated by ORIGINAL real SAP. Their actual diversity
colour belongs to every spoke fork. This includes the empty old base;
the STRONG profiles never acquire a fake logical diagonal.
-/

namespace CCO.TypedOrbitFrames

universe u v w z r
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {B : Type z} [Finite B] (base : B ↪ Sigma X)
variable {i : ι} (q : X i)
variable {G : Type r} [Group G] [∀ j : ι, MulAction G (X j)]

/-- The complete realised type has a NONEMPTY common STRONG fork
intersection, by a genuine two-copy old SAP construction. The auxiliary
atom is unused because its clone graph has no edges. -/
theorem original_common_spoke_fork_atom_exists
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (hq : (⟨i,q⟩ : Sigma X) ∉ Set.range base)
    (auxiliary : S.Atom i i) :
    ∃ e : S.Atom i i, OriginalOrbitForks S base q e := by
  let D := originalOrbitDiagram S base q (⊥ : SimpleGraph Bool) auxiliary
  let f : DiagramHom D := {
    point := originalOrbitTarget base q
    preserves_edge := by
      intro x y hxy a ha
      cases x with
      | inl d =>
        cases y with
        | inl b => exact ha
        | inr b => exact ha
      | inr b =>
        cases y with
        | inl d => exact ha
        | inr c =>
          have hAdj := ((original_orbit_clone_edge_iff S base q
            (⊥ : SimpleGraph Bool) auxiliary b c hxy a).mp ha).1
          exact False.elim hAdj }
  obtain ⟨g,hg,_,_⟩ := DiagramHom.injectivize_of_SAP H sap f
    (∅ : Set (B ⊕ Bool)) (by simp)
    (∅ : Set (Sigma X)) Set.finite_empty
  have hne : g.image (.inr false) ≠ g.image (.inr true) := by
    intro hh
    have h := hg hh
    cases h
  obtain ⟨e,he⟩ := S.some_colour_of_ne (g.point (.inr false))
    (g.point (.inr true)) hne
  have hSpoke (b : Bool) (d : B) :
      S.colour (g.point (.inr b)) (g.point (.inl d)) =
        S.colour q (base d).2 := by
    obtain ⟨a,ha⟩ := S.some_colour_of_ne q (base d).2 (by
      intro hh
      exact hq ⟨d,hh.symm⟩)
    exact (g.preserves_edge (.inr b) (.inl d) (by simp) a ha).trans ha.symm
  exact ⟨e,fun d => ⟨g.point (.inr false),g.point (.inr true),
    g.point (.inl d),hSpoke false d,hSpoke true d,he⟩⟩

end CCO.TypedOrbitFrames
