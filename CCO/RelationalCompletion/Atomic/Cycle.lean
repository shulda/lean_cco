import CCO.RelationalCompletion.Atomic.Fan

/-! Every specified simple cycle of the complete input has a homomorphic
realization in K, using ordinary AP and all actual small induced diagrams. -/
universe u v
namespace CCO.RelationalCompletion.Atomic
variable {P : Palette.{u,v}}

/-- Cycle feasibility is established before semantic CCO is invoked. -/
theorem cycleHomInto_of_AP (K : Model P → Prop) (A : Model P)
    (ap : AP K) (small : SmallSubmodels K A) (C : SimpleCycle A.diagram) :
    ∃ B : Model P, K B ∧ CycleHomInto C B := by
  have hn : 0 < C.length := by have := C.length_ge_three; omega
  let : NeZero C.length := ⟨Nat.ne_of_gt hn⟩
  have hk : C.length - 1 < C.length := by omega
  have hpos : 1 ≤ C.length - 1 := by have := C.length_ge_three; omega
  have hlen : C.length - 1 + 1 = C.length := by omega
  obtain ⟨B, hKB, point, hsort, hpath, hstar⟩ := fanRealized K A ap small C.vertices hk hpos
  have hchord := hstar (Fin.last (C.length-1))
  let pointN : Fin C.length → Fin B.size := fun p => point (Fin.cast hlen.symm p)
  have hsortN : ∀ p, B.tag (pointN p) = A.tag (C.vertices p) := by
    intro p
    exact hsort (Fin.cast hlen.symm p)
  have hcolour : ∀ p, B.colour (pointN p) (pointN (cyclicNext hn p)) =
      A.colour (C.vertices p) (C.vertices (cyclicNext hn p)) := by
    intro p
    by_cases hlast : p.val = C.length - 1
    · have hp : p = ⟨C.length - 1, hk⟩ := Fin.ext hlast
      have hnext : cyclicNext hn p = 0 := by
        apply Fin.ext
        simp only [cyclicNext, Fin.val_zero]
        rw [hlast, hlen, Nat.mod_self]
      have hback : B.colour (pointN ⟨C.length - 1, hk⟩) (pointN 0) =
          A.colour (C.vertices ⟨C.length - 1, hk⟩) (C.vertices 0) := by
        calc
          _ = Model.reverseTagged P (B.colour (point 0) (point (Fin.last (C.length-1)))) := B.colour_reverse _ _
          _ = _ := congrArg (Model.reverseTagged P) hchord
          _ = _ := (A.colour_reverse _ _).symm
      simpa only [← hp, hnext] using hback
    · have hlt : p.val < C.length - 1 := by omega
      have hnext : cyclicNext hn p = ⟨p.val+1, by omega⟩ := by
        apply Fin.ext
        simp only [cyclicNext]
        exact Nat.mod_eq_of_lt (by omega)
      simp only [hnext]
      change B.colour (point ⟨p.val, by omega⟩) (point ⟨p.val+1, by omega⟩) =
        A.colour (C.vertices p) (C.vertices ⟨p.val+1, by omega⟩)
      exact hpath ⟨p.val, hlt⟩
  refine ⟨B, hKB, pointN, hsortN, ?_⟩
  intro p a ha
  have hh := congrArg
    (fun c : Σ _i : P.Sorts, Σ _j : P.Sorts, Option P.Atom => c.2.2) (hcolour p)
  exact hh.trans ha

end CCO.RelationalCompletion.Atomic
