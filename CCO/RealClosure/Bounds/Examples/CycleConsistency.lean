import CCO.SIR.Positive.Direct.CycleWalk
import CCO.SIR.Positive.Direct.SignedWalk
import Mathlib.Data.Fintype.EquivFin

/-! Actual specified simple-cycle homomorphisms force consistency of every
coordinate equality reader and every Boolean gain reader. These are generic
readout lemmas; their concrete source instances supply literal colours. -/
universe u v w z a
namespace CCO.RealClosure.Bounds.Examples.CycleConsistency
open SIR.Positive.Direct
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {V : Type z} (D : PartialDiagram S V)

abbrev Reader := ∀ {i j}, S.Atom i j → Bool

def specifiedGraph : SimpleGraph V where
  Adj x y := ∃ (h : x ≠ y), ∃ a, D.edge x y h = some a
  symm := ⟨by
    rintro x y ⟨h,a,ha⟩
    exact ⟨(Ne.symm h),S.conv a,(D.edge_reverse x y h a).mp ha⟩⟩
  loopless := ⟨fun _ h => h.choose rfl⟩

noncomputable def edgeRead (read : Reader S) (x y : V) : Bool := by
  classical
  exact if h : x ≠ y then (D.edge x y h).map (fun a => read a) |>.getD false else false

theorem edgeRead_of_edge (read : Reader S) {x y : V} (h : x ≠ y)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y)) (ha : D.edge x y h = some a) :
    edgeRead S D read x y = read a := by simp [edgeRead,h,ha]

theorem edgeRead_symm (read : Reader S)
    (hsym : ∀ {i j} (a : S.Atom i j), read (S.conv a) = read a) (x y : V) :
    edgeRead S D read x y = edgeRead S D read y x := by
  classical
  by_cases h : x = y
  · subst y; rfl
  cases he : D.edge x y h with
  | none =>
    have he' : D.edge y x (Ne.symm h) = none := by
      cases he' : D.edge y x (Ne.symm h) with
      | none => rfl
      | some a =>
        have hh := (D.edge_reverse y x (Ne.symm h) a).mp he'
        rw [he] at hh
        cases hh
    simp [edgeRead,h,he,Ne.symm h,he']
  | some a =>
    rw [edgeRead_of_edge S D read h a he,
      edgeRead_of_edge S D read (Ne.symm h) (S.conv a) ((D.edge_reverse x y h a).mp he)]
    exact (hsym a).symm

/-- Unroll the actual cycle homomorphism after reading its points in a common
value space. The endpoint equality is literal, including zero/last indices. -/
theorem cycle_readout {A : Type a} (read : Reader S) (value : ∀ i, X i → A)
    (relation : A → A → Bool)
    (hread : ∀ {i j} (x : X i) (y : X j) (a : S.Atom i j),
      S.colour x y = some a → read a = relation (value i x) (value j y))
    (hcycles : ∀ C : SimpleCycle D, CycleHom C)
    {K : SimpleGraph V} (hK : K ≤ specifiedGraph S D)
    {x : V} (p : K.Walk x x) (hc : p.IsCycle) :
    ∃ f : ℕ → A, f p.length = f 0 ∧ ∀ n < p.length,
      edgeRead S D read (p.getVert n) (p.getVert (n+1)) = relation (f n) (f (n+1)) := by
  let C := cycleOfWalk D (fun _ _ hh => hK hh) p hc
  obtain ⟨point,hpoint⟩ := hcycles C
  let hp : 0 < p.length := lt_of_lt_of_le (by decide : 0 < 3) hc.three_le_length
  let val : Fin p.length → A := fun n => value _ (point n)
  have hstep (n : Fin p.length) :
      edgeRead S D read (C.vertices n) (C.vertices (cyclicNext C.length_pos n)) =
        relation (val n) (val (cyclicNext C.length_pos n)) := by
    obtain ⟨a,ha⟩ := C.specified n
    rw [edgeRead_of_edge S D read (C.next_ne n) a ha]
    exact hread _ _ a (hpoint n a ha)
  let f : ℕ → A := fun n => val ⟨n % p.length,Nat.mod_lt _ hp⟩
  refine ⟨f,?_,?_⟩
  · simp only [f,Nat.mod_self,Nat.zero_mod]
  · intro n hn
    let i : Fin p.length := ⟨n,hn⟩
    have hi : (⟨n % p.length,Nat.mod_lt _ hp⟩ : Fin p.length) = i :=
      Fin.ext (Nat.mod_eq_of_lt hn)
    have hnext : p.getVert ((n+1) % p.length) = p.getVert (n+1) :=
      closedWalk_next_getVert p hp i
    have hh := hstep i
    change edgeRead S D read (p.getVert n) (p.getVert ((n+1)%p.length)) =
      relation (val i) (val ⟨(n+1)%p.length,_⟩) at hh
    change edgeRead S D read (p.getVert n) (p.getVert (n+1)) =
      relation (val ⟨n%p.length,_⟩) (val ⟨(n+1)%p.length,_⟩)
    rw [hi]
    rwa [hnext] at hh

def equalityGraph (read : Reader S)
    (hsym : ∀ {i j} (a : S.Atom i j), read (S.conv a) = read a) : SimpleGraph V where
  Adj x y := (specifiedGraph S D).Adj x y ∧ edgeRead S D read x y = true
  symm := ⟨by
    intro x y h
    exact ⟨h.1.symm,(edgeRead_symm S D read hsym x y).symm.trans h.2⟩⟩
  loopless := ⟨fun x h => h.1.ne rfl⟩

/-- A specified inequality cannot join endpoints of an equality path. The
short simple path plus that single edge is a genuine specified simple cycle. -/
theorem inequality_not_reachable (read : Reader S)
    (hsym : ∀ {i j} (a : S.Atom i j), read (S.conv a) = read a)
    (value : ∀ i, X i → ℕ)
    (hvalue : ∀ {i j} (x : X i) (y : X j) (a : S.Atom i j),
      S.colour x y = some a → (value i x = value j y ↔ read a = true))
    (hcycles : ∀ C : SimpleCycle D, CycleHom C)
    {x y : V} (hxy : (specifiedGraph S D).Adj x y)
    (hread : edgeRead S D read x y = false) :
    ¬ (equalityGraph S D read hsym).Reachable x y := by
  classical
  intro hreach
  let path := hreach.some.toPath
  let p := path.val
  have hp : p.IsPath := path.property
  have hp0 : p.length ≠ 0 := fun hz => hxy.ne (SimpleGraph.Walk.length_eq_zero_iff.mp hz).eq
  have hp1 : p.length ≠ 1 := by
    intro ho
    have ha := SimpleGraph.Walk.adj_of_length_eq_one ho
    have hh := ha.2
    rw [hread] at hh
    cases hh
  have hp2 : 2 ≤ p.length := by omega
  let q := p.reverse
  have hsub : equalityGraph S D read hsym ≤ specifiedGraph S D :=
    fun _ _ hh => hh.1
  let r : (specifiedGraph S D).Walk y x := q.mapLe hsub
  let closed : (specifiedGraph S D).Walk x x := .cons hxy r
  have hclosed : closed.IsCycle := by
    apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    constructor
    · dsimp only [closed]
      rw [SimpleGraph.Walk.tail_cons]
      exact (SimpleGraph.Walk.isPath_copy r (SimpleGraph.Walk.getVert_zero r).symm rfl).mpr
        (hp.reverse.mapLe _)
    · simpa only [closed,r,q,SimpleGraph.Walk.length_cons,SimpleGraph.Walk.length_mapLe,
        SimpleGraph.Walk.length_reverse] using (show 3 ≤ p.length + 1 by omega)
  have hreadout : ∀ {i j} (a : X i) (b : X j) (c : S.Atom i j),
      S.colour a b = some c → read c = decide (value i a = value j b) := by
    intro i j a b c hc
    have hh := hvalue a b c hc
    cases hr : read c <;> simp_all
  obtain ⟨f,hend,hsteps⟩ := cycle_readout S D read value (fun a b => decide (a=b))
    hreadout hcycles (fun _ _ h => h) closed hclosed
  have hfirst : f 0 ≠ f 1 := by
    have hh : edgeRead S D read x y = decide (f 0 = f 1) := by
      simpa only [closed,Nat.zero_add,SimpleGraph.Walk.getVert_zero,
        SimpleGraph.Walk.getVert_cons_succ] using hsteps 0 (by simp [closed])
    rw [hread] at hh
    exact of_decide_eq_false hh.symm
  have hrest (n : ℕ) (hn : n < q.length) : f (n+1) = f (n+1+1) := by
    have hh := hsteps (n+1) (by simp only [closed,r,SimpleGraph.Walk.length_cons,
      SimpleGraph.Walk.length_mapLe]; omega)
    have heq0 : closed.getVert (n+1) = q.getVert n := by simp [closed,r,SimpleGraph.Walk.mapLe]
    have heq1 : closed.getVert (n+1+1) = q.getVert (n+1) := by simp [closed,r,SimpleGraph.Walk.mapLe]
    rw [heq0,heq1,(q.adj_getVert_succ hn).2] at hh
    exact of_decide_eq_true hh.symm
  have hall (n : ℕ) : n ≤ q.length → f 1 = f (n+1) := by
    induction n with
    | zero => intro _; rfl
    | succ n ih => intro hn; exact (ih (by omega)).trans (hrest n (by omega))
  have hlen : closed.length = q.length + 1 := by simp [closed,r]
  have hh := hall q.length le_rfl
  rw [← hlen,hend] at hh
  exact hfirst hh.symm

/-- Finite equality components receive distinct natural labels. -/
theorem coordinate_labels (read : Reader S)
    (hsym : ∀ {i j} (a : S.Atom i j), read (S.conv a) = read a)
    (value : ∀ i, X i → ℕ)
    (hvalue : ∀ {i j} (x : X i) (y : X j) (a : S.Atom i j),
      S.colour x y = some a → (value i x = value j y ↔ read a = true))
    (hcycles : ∀ C : SimpleCycle D, CycleHom C) :
    ∃ label : V → ℕ, ∀ x y (h : x ≠ y) (a : S.Atom (D.vertexSort x) (D.vertexSort y)),
      D.edge x y h = some a → (label x = label y ↔ read a = true) := by
  classical
  let K := equalityGraph S D read hsym
  letI : Finite V := D.finite_type
  letI : Fintype K.ConnectedComponent := Fintype.ofFinite _
  let code : K.ConnectedComponent → ℕ := fun c => (Fintype.equivFin _ c).val
  have hcode : Function.Injective code := Fin.val_injective.comp (Fintype.equivFin _).injective
  let label := fun x => code (K.connectedComponentMk x)
  refine ⟨label,?_⟩
  intro x y h a ha
  have hedge : (specifiedGraph S D).Adj x y := ⟨h,a,ha⟩
  have hr := edgeRead_of_edge S D read h a ha
  constructor
  · intro heq
    have hreach : K.Reachable x y := SimpleGraph.ConnectedComponent.exact (hcode heq)
    by_contra hn
    have hf : read a = false := Bool.eq_false_iff.mpr hn
    exact inequality_not_reachable S D read hsym value hvalue hcycles hedge (hr.trans hf) hreach
  · intro heq
    exact congrArg code (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      (show K.Adj x y from ⟨hedge,hr.trans heq⟩))

/-- Boolean gains integrate once actual cycle homomorphisms make every simple
closed-walk gain vanish. No independent coherence/provider premise is used. -/
theorem phase_labels (read : Reader S)
    (hsym : ∀ {i j} (a : S.Atom i j), read (S.conv a) = read a)
    (value : ∀ i, X i → Bool)
    (hvalue : ∀ {i j} (x : X i) (y : X j) (a : S.Atom i j),
      S.colour x y = some a → (value i x ^^ value j y) = read a)
    (hcycles : ∀ C : SimpleCycle D, CycleHom C) :
    ∃ phase : V → Bool, ∀ x y (h : x ≠ y) (a : S.Atom (D.vertexSort x) (D.vertexSort y)),
      D.edge x y h = some a → (phase x ^^ phase y) = read a := by
  have hcycle : ∀ x (p : (specifiedGraph S D).Walk x x), p.IsCycle →
      SignedWalk.parity (edgeRead S D read) p = false := by
    intro x p hp
    obtain ⟨f,hend,hsteps⟩ := cycle_readout S D read value (fun a b => a ^^ b)
      (fun _ _ a h => (hvalue _ _ a h).symm) hcycles (fun _ _ h => h) p hp
    have hh := SignedWalk.parity_of_getVert (edgeRead S D read) p f hsteps
    simpa only [hend,Bool.xor_self] using hh
  have hclosed := SignedWalk.closed_parity_zero (edgeRead S D read)
    (edgeRead_symm S D read hsym) hcycle
  obtain ⟨phase,hphase⟩ := SignedWalk.exists_potential (edgeRead S D read) hclosed
  refine ⟨phase,?_⟩
  intro x y h a ha
  exact (hphase x y ⟨h,a,ha⟩).symm.trans (edgeRead_of_edge S D read h a ha)
end CCO.RealClosure.Bounds.Examples.CycleConsistency
