import CCO.RealClosure.Bounds.Examples.CycleConsistency

/-! Optional signed constraints are integrated only on their actual signed
edges. An unsigned edge imposes no phase equation. Simple-cycle feasibility
supplies all consistency; there is no independent potential premise. -/
universe u v w z
namespace CCO.OrbitalCover.Example.Potentials
open CCO.SIR.Positive.Direct
open CCO.RealClosure.Bounds.Examples.CycleConsistency

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {V : Type z} (D : PartialDiagram S V)

abbrev OptionalReader := ∀ {i j}, S.Atom i j → Option Bool

def signedGraph (read : OptionalReader S)
    (hsym : ∀ {i j} (a : S.Atom i j), read (S.conv a) = read a) : SimpleGraph V where
  Adj x y := ∃ (h : x ≠ y), ∃ a, D.edge x y h = some a ∧ (read a).isSome = true
  symm := ⟨by
    rintro x y ⟨h,a,ha,hr⟩
    exact ⟨h.symm,S.conv a,(D.edge_reverse x y h a).mp ha,by simpa only [hsym] using hr⟩⟩
  loopless := ⟨fun _ h => h.choose rfl⟩

theorem signedGraph_le (read : OptionalReader S)
    (hsym : ∀ {i j} (a : S.Atom i j), read (S.conv a) = read a) :
    signedGraph S D read hsym ≤ specifiedGraph S D := by
  rintro x y ⟨h,a,ha,_⟩
  exact ⟨h,a,ha⟩

/-- Read actual old simple-cycle homomorphisms on the signed subgraph.
No condition is imposed on the unspecified sign of an unsigned edge. -/
theorem signed_cycle_readout (read : OptionalReader S)
    (hsym : ∀ {i j} (a : S.Atom i j), read (S.conv a) = read a)
    (value : ∀ i, X i → Bool)
    (hvalue : ∀ {i j} (x : X i) (y : X j) (a : S.Atom i j) (b : Bool),
      S.colour x y = some a → read a = some b → (value i x ^^ value j y) = b)
    (hcycles : ∀ C : SimpleCycle D, CycleHom C)
    {x : V} (p : (signedGraph S D read hsym).Walk x x) (hc : p.IsCycle) :
    ∃ f : ℕ → Bool, f p.length = f 0 ∧ ∀ n < p.length,
      edgeRead S D (fun a => (read a).getD false) (p.getVert n) (p.getVert (n+1)) =
        (f n ^^ f (n+1)) := by
  let K := signedGraph S D read hsym
  let hK := fun x y h => signedGraph_le S D read hsym (v := x) (w := y) h
  let C := cycleOfWalk D hK p hc
  obtain ⟨point,hpoint⟩ := hcycles C
  let hp : 0 < p.length := lt_of_lt_of_le (by decide : 0 < 3) hc.three_le_length
  let val : Fin p.length → Bool := fun n => value _ (point n)
  have hstep (n : Fin p.length) :
      edgeRead S D (fun a => (read a).getD false)
        (C.vertices n) (C.vertices (cyclicNext C.length_pos n)) =
        (val n ^^ val (cyclicNext C.length_pos n)) := by
    have hadj : K.Adj (C.vertices n) (C.vertices (cyclicNext C.length_pos n)) := by
      change K.Adj (p.getVert n.val) (p.getVert ((n.val+1)%p.length))
      rw [closedWalk_next_getVert p hp n]
      exact p.adj_getVert_succ n.isLt
    obtain ⟨hne,a,ha,hr⟩ := hadj
    have hsome : ∃ b, read a = some b := Option.isSome_iff_exists.mp hr
    obtain ⟨b,hb⟩ := hsome
    rw [edgeRead_of_edge S D (fun a => (read a).getD false) hne a ha,hb]
    exact (hvalue _ _ a b (hpoint n a ha) hb).symm
  let f : ℕ → Bool := fun n => val ⟨n % p.length,Nat.mod_lt _ hp⟩
  refine ⟨f,?_,?_⟩
  · simp only [f,Nat.mod_self,Nat.zero_mod]
  · intro n hn
    let i : Fin p.length := ⟨n,hn⟩
    have hi : (⟨n % p.length,Nat.mod_lt _ hp⟩ : Fin p.length) = i :=
      Fin.ext (Nat.mod_eq_of_lt hn)
    have hnext : p.getVert ((n+1)%p.length) = p.getVert (n+1) :=
      closedWalk_next_getVert p hp i
    have hh := hstep i
    change edgeRead S D (fun a => (read a).getD false)
      (p.getVert n) (p.getVert ((n+1)%p.length)) =
      (val i ^^ val ⟨(n+1)%p.length,_⟩) at hh
    change edgeRead S D (fun a => (read a).getD false)
      (p.getVert n) (p.getVert (n+1)) =
      (val ⟨n%p.length,_⟩ ^^ val ⟨(n+1)%p.length,_⟩)
    rw [hi]
    rwa [hnext] at hh

/-- Actual simple cycles suffice for one optional signed coordinate. -/
theorem optional_phase_labels (read : OptionalReader S)
    (hsym : ∀ {i j} (a : S.Atom i j), read (S.conv a) = read a)
    (value : ∀ i, X i → Bool)
    (hvalue : ∀ {i j} (x : X i) (y : X j) (a : S.Atom i j) (b : Bool),
      S.colour x y = some a → read a = some b → (value i x ^^ value j y) = b)
    (hcycles : ∀ C : SimpleCycle D, CycleHom C) :
    ∃ phase : V → Bool, ∀ x y (h : x ≠ y) (a : S.Atom (D.vertexSort x) (D.vertexSort y))
      (b : Bool), D.edge x y h = some a → read a = some b →
      (phase x ^^ phase y) = b := by
  let K := signedGraph S D read hsym
  let weight := edgeRead S D (fun a => (read a).getD false)
  have hcycle : ∀ x (p : K.Walk x x), p.IsCycle → SignedWalk.parity weight p = false := by
    intro x p hp
    obtain ⟨f,hend,hsteps⟩ := signed_cycle_readout S D read hsym value hvalue hcycles p hp
    have hh := SignedWalk.parity_of_getVert weight p f hsteps
    simpa only [hend,Bool.xor_self] using hh
  have hclosed := SignedWalk.closed_parity_zero weight
    (edgeRead_symm S D (fun a => (read a).getD false) (fun a => by rw [hsym])) hcycle
  obtain ⟨phase,hphase⟩ := SignedWalk.exists_potential weight hclosed
  refine ⟨phase,?_⟩
  intro x y h a b ha hb
  have hadj : K.Adj x y := ⟨h,a,ha,by change (read a).isSome = true; rw [hb]; rfl⟩
  have hh := (hphase x y hadj).symm
  dsimp only [weight] at hh
  rw [edgeRead_of_edge S D (fun a => (read a).getD false) h a ha,hb] at hh
  exact hh

end CCO.OrbitalCover.Example.Potentials
