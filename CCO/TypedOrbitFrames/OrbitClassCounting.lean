import CCO.TypedOrbitFrames.OrbitCompletion
import CCO.ParityHasse.Sparse.Existence
import CCO.TerminalLattice.StrongPaletteBridge

/-!
# Source11 T02: high-chromatic counting for the exact old one-point type

After ONE whole-diagram completion over the literal old base, the genuine
J-classes of its clone images properly colour the chosen graph. No global
clone injectivity or separate per-coordinate realisations are needed.
-/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Sparse CCO.ParityHasse.Original CCO.RealClosure.Bounds

universe u v w z r
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {B : Type z} [Finite B]
variable (base : B ↪ Sigma X) {i : ι} (q : X i)
variable {G : Type r} [Group G] [∀ j : ι, MulAction G (X j)]

/-- Actual quotient points realised by the SAME complete original
one-point type over the SAME pinned old base. -/
def originalExactTypeClasses (J : ColourEq S i) : Set (Quotient J.val) :=
  {c | ∃ x : X i, (∀ d : B, S.colour x (base d).2 =
      S.colour q (base d).2) ∧ Quotient.mk J.val x = c}

/-- The high-chromatic part of T02, with every old graph/triangle/cycle
and common-base alignment provider discharged. The atom premise is
precisely the source's choice `e ∈ C_p \ J`, not a whole-diagram or orbit
realisation premise. -/
theorem original_exact_type_classes_infinite_of_external_fork_atom
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,z,w} S) (nr2 : SortNR2 S i)
    (hq : (⟨i,q⟩ : Sigma X) ∉ Set.range base)
    (J : ColourEq S i) (e : S.Atom i i)
    (hfork : OriginalOrbitForks S base q e)
    (he : e ∉ CCO.TerminalLattice.originalEquivDiversityPalette S J) :
    (originalExactTypeClasses S base q J).Infinite := by
  classical
  intro hFinite
  let classes := originalExactTypeClasses S base q J
  letI : Fintype ↥classes := hFinite.fintype
  let n := Fintype.card ↥classes + 1
  have hn : 0 < n := Nat.succ_pos _
  obtain ⟨N,hN⟩ := original_orbit_diagram_completion_threshold
    S base q e H sap cco nr2 hq hfork
  obtain ⟨W⟩ := high_girth_chromatic_exists hn (max 3 (N.val + 1))
  let D := originalOrbitDiagram S base q W.graph e
  obtain ⟨f,hf⟩ := hN W.graph W.noShortCycles
  have hSpokes (v : Fin W.size) (d : B) :
      S.colour (f.point (.inr v)) (base d).2 = S.colour q (base d).2 := by
    obtain ⟨a,ha⟩ := S.some_colour_of_ne q (base d).2 (by
      intro hh
      exact hq ⟨d,hh.symm⟩)
    have h := f.preserves_edge (.inr v) (.inl d) (by simp) a ha
    rw [hf d] at h
    exact h.trans ha.symm
  let c : Fin W.size → ↥classes := fun v =>
    ⟨Quotient.mk J.val (f.point (.inr v)),
      ⟨f.point (.inr v),hSpokes v,rfl⟩⟩
  let κ : Fin W.size → Fin n := fun v =>
    Fin.castLE (by dsimp [n]; omega) (Fintype.equivFin ↥classes (c v))
  obtain ⟨v,w,hvw,hκ⟩ := W.monochromatic κ
  have hValues : ((Fintype.equivFin ↥classes) (c v)).val =
      ((Fintype.equivFin ↥classes) (c w)).val := by
    change (κ v).val = (κ w).val
    exact congrArg Fin.val hκ
  have hc : c v = c w := (Fintype.equivFin ↥classes).injective (Fin.ext hValues)
  have hJ : J (f.point (.inr v)) (f.point (.inr w)) :=
    Quotient.exact (congrArg Subtype.val hc)
  have hcol : S.colour (f.point (.inr v)) (f.point (.inr w)) = some e := by
    apply f.preserves_edge (.inr v) (.inr w) (by
      intro hh
      exact hvw.ne (Sum.inr.inj hh)) e
    exact (original_orbit_clone_edge_iff S base q W.graph e v w _ e).mpr ⟨hvw,rfl⟩
  exact he ⟨f.point (.inr v),f.point (.inr w),hJ,hcol⟩

end CCO.TypedOrbitFrames
