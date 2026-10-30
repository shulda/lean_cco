import CCO.PositiveWords
import CCO.RawExact.ConvolutionFromHelly
import CCO.StrongExact.ExactMenus

/-! B047 C56. A positive STRONG word family has an actual FULL RAW
presentation before taking its meet. The correspondence is always guarded
by a genuine endpoint diversity atom. -/

universe u v w t
namespace CCO.PairSafeSplit.Strong
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)

include H sap in
theorem profile_iff_represented {i j : ι} (p : PositiveWord S i j)
    {x : X i} {y : X j} {a : S.Atom i j} (hc : S.colour x y = some a) :
    a ∈ PositiveWord.profile S p ↔ PositiveWord.represented S p x y := by
  constructor
  · intro h
    rw [← PositiveWord.diversityGuard_represented_eq_profile_of_SAP S H sap p] at h
    obtain ⟨x',y',hr,hcol⟩ := h
    obtain ⟨g,hgx,hgy⟩ := S.pair_homogeneous_of_homogeneous H x' x y' y (hcol.trans hc.symm)
    simpa only [hgx,hgy] using PositiveWord.represented_invariant_of_homogeneous S H p g x' y' hr
  · intro h
    rw [← PositiveWord.diversityGuard_represented_eq_profile_of_SAP S H sap p]
    exact ⟨x,y,h,hc⟩

include H sap in
def rawPresentation {i j : ι} (p : PositiveWord S i j) : RawExact.NonemptyExact S i j := by
  apply RawExact.singletonExact S (PositiveWord.toRawWord S p)
  obtain ⟨a,ha⟩ := PositiveWord.profile_nonempty_of_SAP S H sap p
  rw [← PositiveWord.diversityGuard_rawWord_eq_profile_of_SAP S H sap p] at ha
  obtain ⟨x,y,hxy,_⟩ := ha
  exact ⟨x,y,hxy⟩

theorem rawPresentation_relation {i j : ι} (p : PositiveWord S i j) :
    RawExact.evaluate S (rawPresentation S H sap p).words = PositiveWord.represented S p := by
  change RawExact.evaluate S [PositiveWord.toRawWord S p] = _
  rw [RawExact.evaluate_single,← PositiveWord.represented_toRawWord]

def rawFamily {i j : ι} (ps : List (PositiveWord S i j)) : List (RawExact.NonemptyExact S i j) :=
  ps.map (rawPresentation S H sap)

theorem rawFamily_relation {i j : ι} (ps : List (PositiveWord S i j)) (x : X i) (y : X j) :
    (∀ d ∈ rawFamily S H sap ps, RawExact.evaluate S d.words x y) ↔
      ∀ p ∈ ps, PositiveWord.represented S p x y := by
  simp only [rawFamily,List.forall_mem_map,rawPresentation_relation]

theorem rawFamily_guard {i j : ι} (ps : List (PositiveWord S i j))
    {x : X i} {y : X j} {a : S.Atom i j} (hc : S.colour x y = some a) :
    (∀ d ∈ rawFamily S H sap ps, RawExact.evaluate S d.words x y) ↔
      a ∈ StrongExact.present S ps := by
  rw [rawFamily_relation]
  change (∀ p ∈ ps, PositiveWord.represented S p x y) ↔
    ∀ p ∈ ps, a ∈ PositiveWord.profile S p
  constructor
  · intro h p hp
    exact (profile_iff_represented S H sap p hc).mpr (h p hp)
  · intro h p hp
    exact (profile_iff_represented S H sap p hc).mp (h p hp)

theorem rawFamily_nonempty {i j : ι} (ps : List (PositiveWord S i j))
    (hne : (StrongExact.present S ps).Nonempty) :
    TRel.Nonempty (fun x y => ∀ d ∈ rawFamily S H sap ps, RawExact.evaluate S d.words x y) := by
  obtain ⟨a,ha⟩ := hne
  obtain ⟨x,y,hc⟩ := S.realized a
  exact ⟨x,y,(rawFamily_guard S H sap ps hc).mpr ha⟩

end CCO.PairSafeSplit.Strong
