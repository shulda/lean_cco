import CCO.TerminalPowers.WholeSource
import CCO.TerminalPowers.GraphConsequences

/-! A downstream use of the actual terminal-power theorem: ONE positive
threshold gives both the literal palette equality and actual injective paths
of EVERY later length with BOTH prescribed real endpoints unchanged. -/
universe u v w
namespace CCO.TerminalPowers
open ParityHasse.Original RealClosure.Bounds
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

theorem all_large_powers_with_fixed_paths (H : HomogeneousSource S (FullAut S))
    (sap : AgeSAP S) (i : ι) (nr2 : FullSortNR2 S i) (t : S.Atom i i) :
    ∃ N : ℕ+, (connectivityPalette S H t).Nonempty ∧ ∀ n : ℕ+, N.val ≤ n.val →
      purePower S t n = connectivityPalette S H t ∧
      ∀ c ∈ connectivityPalette S H t, ∀ x y : X i, S.atomRel c x y →
        ∃ f : Fin (n.val+1) ↪ X i, f 0 = x ∧ f (Fin.last n.val) = y ∧
          ∀ p : Fin n.val, S.atomRel t (f p.castSucc) (f p.succ) := by
  obtain ⟨N,hpower⟩ := terminal_pure_power_full S H sap i nr2 t
  obtain ⟨M,hM,hwalk⟩ := uniform_represented_threshold S H (sortNR2_of_full S i nr2) t
  let K : ℕ+ := ⟨max N.val M,lt_of_lt_of_le N.property (Nat.le_max_left _ _)⟩
  refine ⟨K,connectivityPalette_nonempty S H t,?_⟩
  intro n hn
  have hnN : N.val ≤ n.val := (Nat.le_max_left _ M).trans hn
  have hnM : M ≤ n.val := (Nat.le_max_right N.val _).trans hn
  refine ⟨hpower n hnN,?_⟩
  intro c hc x y hcol
  have hxy : x ≠ y := fun he => S.atomRel_ne hcol (congrArg (Sigma.mk i) he)
  obtain ⟨g,hinj,hfirst,hlast,hedge⟩ := injective_path_fixed_endpoints S H sap t
    n.property hxy (hwalk n.val hnM x y (hc x y hcol))
  let f : Fin (n.val+1) ↪ X i := {
    toFun p := g.point p
    inj' := fun _ _ he => hinj (congrArg (Sigma.mk i) he) }
  exact ⟨f,hfirst,hlast,hedge⟩

end CCO.TerminalPowers
