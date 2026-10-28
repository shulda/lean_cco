import CCO.SIR.Positive.Direct.Constraints

/-! Real homomorphisms of the specified simple cycles force all signed
closed-walk parities to vanish. -/

universe z

namespace CCO.SIR.Positive.Direct

variable {V : Type z} (D : PartialDiagram source V)

/-- Unroll the actual homomorphism of the simple cycle associated to a walk.
The endpoint is literally the initial point, including its parent and sheet.
-/
theorem realization_of_cycleWalk {K : SimpleGraph V}
    (hK : ∀ x y, K.Adj x y → ∃ (h : x ≠ y), ∃ a, D.edge x y h = some a)
    (hcycles : ∀ C : SimpleCycle D, CycleHom C)
    {x : V} (p : K.Walk x x) (hc : p.IsCycle) :
    ∃ f : ℕ → Point, f p.length = f 0 ∧
      ∀ n (hn : n < p.length) (h : p.getVert n ≠ p.getVert (n + 1)) a,
        D.edge (p.getVert n) (p.getVert (n + 1)) h = some a →
          colour (f n) (f (n + 1)) = some a := by
  let C := cycleOfWalk D hK p hc
  obtain ⟨point,hpoint⟩ := hcycles C
  dsimp only [C,cycleOfWalk] at point hpoint
  let hp : 0 < p.length := lt_of_lt_of_le (by decide : 0 < 3) hc.three_le_length
  let real : Fin p.length → Point := point
  let f : ℕ → Point := fun n => real ⟨n % p.length, Nat.mod_lt _ hp⟩
  refine ⟨f, ?_, ?_⟩
  · simp only [f,Nat.mod_self,Nat.zero_mod]
  · intro n hn h a ha
    let i : Fin p.length := ⟨n,hn⟩
    have hnedge : p.getVert n ≠ p.getVert ((n+1) % p.length) := by
      rw [closedWalk_next_getVert p hp i]
      exact h
    have hnext : p.getVert ((n+1) % p.length) = p.getVert (n+1) :=
      closedWalk_next_getVert p hp i
    have hedge : D.edge (p.getVert n) (p.getVert ((n+1) % p.length))
        hnedge = some a := by
      have transport (y y' : V) (heq : y = y')
          (h0 : p.getVert n ≠ y) (h1 : p.getVert n ≠ y') :
          D.edge (p.getVert n) y h0 = D.edge (p.getVert n) y' h1 := by
        cases heq
        rfl
      exact (transport _ _ hnext hnedge h).trans ha
    have hh := hpoint i a hedge
    change colour (real i) (real (cyclicNext hp i)) = some a at hh
    change colour (real ⟨n % p.length,_⟩) (real ⟨(n+1) % p.length,_⟩) = some a
    have hi : (⟨n % p.length, Nat.mod_lt _ hp⟩ : Fin p.length) = i := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt hn
    rw [hi]
    exact hh

theorem cycle_sign_zero
    (hcycles : ∀ C : SimpleCycle D, CycleHom C)
    {x : V} (p : (edGraph D).Walk x x) (hc : p.IsCycle) :
    SignedWalk.parity (sign D) p = false := by
  have hK : ∀ x y, (edGraph D).Adj x y →
      ∃ (h : x ≠ y), ∃ a, D.edge x y h = some a :=
    fun _ _ h => edGraph_le_specifiedGraph D h
  obtain ⟨f,hclosed,hsteps⟩ := realization_of_cycleWalk D hK hcycles p hc
  have hh := SignedWalk.parity_of_getVert (sign D) p (fun n => sheet (f n))
    (fun n hn => sign_of_realized_edge D (p.adj_getVert_succ hn) _ _
      (fun h a ha => hsteps n hn h a ha))
  simpa only [hclosed,Bool.xor_self] using hh

theorem closed_sign_zero
    (hcycles : ∀ C : SimpleCycle D, CycleHom C)
    (x : V) (p : (edGraph D).Walk x x) :
    SignedWalk.parity (sign D) p = false :=
  SignedWalk.closed_parity_zero (sign D) (sign_symm D)
    (fun _ p hc => cycle_sign_zero D hcycles p hc) x p

end CCO.SIR.Positive.Direct
