import CCO.RealClosure.Bounds.Examples.CoordinateClosure
import CCO.StabilizerSAP

/-! A real off-base coordinate corner is fixed by the actual full stabilizer.
The accepted actual-SAP duplication theorem therefore rules out SAP. -/
universe u
namespace CCO.RealClosure.Bounds.Examples.Coordinate
variable (I : Type u) [Fintype I] [DecidableEq I]

theorem offbase_fixed_notSAP (A : Finset (Point I)) (x : Point I)
    (hx : x ∉ A) (hfixed : x ∈ Dcl (Aut I) A) : ¬ AgeSAP (source I) := by
  classical
  intro hsap
  let tag : Point I → Sigma (fun _ : Unit => Point I) := fun y => ⟨(),y⟩
  let B : FiniteInduced (X := fun _ : Unit => Point I) :=
    FiniteInduced.ofFinset (A.image tag)
  have htag (y : Point I) (hy : y ∈ A) : tag y ∈ B.vertices := by
    exact Finset.mem_image.mpr ⟨y,hy,rfl⟩
  have hxB : tag x ∉ B.vertices := by
    rintro hy
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hy
    have hxy : y = x := congrArg (fun z : Sigma (fun _ : Unit => Point I) => z.2) he
    exact hx (hxy ▸ hy)
  have hfin : (RealAction.orbitOver (G := Aut I) B.vertices (tag x)).Finite := by
    apply Set.Finite.subset (Set.finite_singleton (tag x))
    rintro y ⟨g,hg,rfl⟩
    have hga : ∀ a ∈ A, g • a = a := by
      intro a ha
      exact congrArg (fun z : Sigma (fun _ : Unit => Point I) => z.2)
        (hg (tag a) (htag a ha))
    exact Set.mem_singleton_iff.mpr (congrArg tag (hfixed g hga))
  exact RealAction.infinite_stabilizer_orbit_of_SAP (source I) (homogeneous I) hsap B (tag x) hxB hfin

theorem corner_fixed {i j : I} (hij : i ≠ j) :
    (fun _ : I => (0 : ℕ)) ∈ Dcl (Aut I) ({axisPoint I i 1,axisPoint I j 1} : Finset (Point I)) := by
  classical
  apply grid_fixed I
  intro k
  by_cases hki : k = i
  · subst k
    apply Finset.mem_image.mpr
    exact ⟨axisPoint I j 1,Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
      by simp [axisPoint,hij]⟩
  · apply Finset.mem_image.mpr
    exact ⟨axisPoint I i 1,Finset.mem_insert_self _ _,by simp [axisPoint,hki]⟩

theorem corner_outside {i j : I} :
    (fun _ : I => (0 : ℕ)) ∉ ({axisPoint I i 1,axisPoint I j 1} : Finset (Point I)) := by
  classical
  intro h
  rcases Finset.mem_insert.mp h with he | he
  · have hh := congrFun he i
    simpa [axisPoint] using hh
  · have hh := congrFun (Finset.mem_singleton.mp he) j
    simpa [axisPoint] using hh

theorem notSAP_of_two_coordinates {i j : I} (hij : i ≠ j) : ¬ AgeSAP (source I) :=
  offbase_fixed_notSAP I _ _ (corner_outside I) (corner_fixed I hij)
end CCO.RealClosure.Bounds.Examples.Coordinate
