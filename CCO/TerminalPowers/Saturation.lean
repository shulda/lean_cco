import CCO.TerminalPowers.PositivePower
import CCO.TerminalPowers.PinnedPath

/-! Actual injective paths read out positive STRONG powers. The final
source theorem combines the independent graph and SAP branches. -/
universe u v w t
namespace CCO.TerminalPowers
open ParityHasse.Original RealClosure.Bounds
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X) {i : ι}

/-- A literal injective positive finite line has the genuine iterated
STRONG endpoint profile. No SAP or NR2 is needed for this readout. -/
theorem profile_of_injective_points (t : S.Atom i i) (n : Nat)
    (f : Fin (n+2) → X i) (hinj : Function.Injective f)
    (hedge : ∀ p : Fin (n+1), S.atomRel t (f p.castSucc) (f p.succ))
    {c : S.Atom i i} (hc : S.atomRel c (f 0) (f (Fin.last (n+1)))) :
    c ∈ PositiveWord.profile S (repeatedWord S t n) := by
  induction n generalizing c with
  | zero =>
    have he := (hedge 0).symm.trans hc
    exact (Option.some.inj he).symm
  | succ n ih =>
    have hne : (⟨i,f (1 : Fin (n+3))⟩ : Sigma X) ≠ ⟨i,f (Fin.last (n+2))⟩ := by
      intro he
      have hp := hinj (eq_of_heq (Sigma.mk.inj he).2)
      have hv := congrArg Fin.val hp
      simp only [Fin.val_one,Fin.val_last] at hv
      omega
    obtain ⟨b,hb⟩ := S.some_colour_of_ne (f (1 : Fin (n+3))) (f (Fin.last (n+2))) hne
    have htail : b ∈ PositiveWord.profile S (repeatedWord S t n) :=
      ih (fun p => f p.succ) (fun _ _ h => Fin.succ_injective _ (hinj h))
        (fun p => hedge p.succ) hb
    exact ⟨t,rfl,b,htail,f 0,f 1,f (Fin.last (n+2)),hedge 0,hb,hc⟩

/-- A fully injective path fixes an actual diversity endpoint colour in
the positive-only power API. -/
theorem purePower_of_injective_path (t : S.Atom i i) (n : ℕ+)
    (f : DiagramHom (pathDiagram S t n.val)) (hinj : f.IsInjective)
    (hedge : ∀ p : Fin n.val, S.colour (f.point p.castSucc) (f.point p.succ) = some t)
    {c : S.Atom i i} (hc : S.colour (f.point 0) (f.point (Fin.last n.val)) = some c) :
    c ∈ purePower S t n := by
  rcases n with ⟨n,hn⟩
  cases n with
  | zero => omega
  | succ n =>
    let point : Fin (n+2) → X i := fun p => f.point p
    have hi : Function.Injective point := by
      intro a b h
      exact hinj (congrArg (Sigma.mk i) h)
    have hp := profile_of_injective_points S t n point hi hedge hc
    rw [repeatedWord_profile] at hp
    exact hp

variable {G : Type t} [Group G] [∀ j, MulAction G (X j)] (H : HomogeneousSource S G)

/-- C19/C21 and lem:typed-terminal-pure-power / its TPP equation. The ONE
positive threshold works for EVERY later positive exponent and actual pair. -/
theorem terminal_pure_power (sap : AgeSAP S) (nr2 : SortNR2 S i) (t : S.Atom i i) :
    ∃ N : ℕ+, ∀ n : ℕ+, N.val ≤ n.val → purePower S t n = connectivityPalette S H t := by
  obtain ⟨N,hN,hwalk⟩ := uniform_represented_threshold S H nr2 t
  refine ⟨⟨N,hN⟩,?_⟩
  intro n hn
  apply Set.Subset.antisymm
  · exact purePower_subset_connectivity S H t n
  · intro c hc
    obtain ⟨x,y,hxy,hcol,hconn⟩ := connectivityPalette_representative S H t hc
    obtain ⟨f,hinj,hfirst,hlast,hedges⟩ := injective_path_fixed_endpoints S H sap t
      n.property hxy (hwalk n.val hn x y hconn)
    apply purePower_of_injective_path S t n f hinj hedges
    have he : S.colour (f.point 0 : X i) (f.point (Fin.last n.val) : X i) = S.colour x y :=
      congrArg₂ (fun a b : X i => S.colour a b) hfirst hlast
    exact he.trans hcol

end CCO.TerminalPowers
