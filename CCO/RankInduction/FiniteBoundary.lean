import CCO.RankInduction.Basis

/-! Finite sources are direct: the same literal universe extends all
requests and moves every selected root into the nonempty original input.
Neither CCO nor an EPPA or owner-master premise is used. -/

universe v w t
namespace CCO.RankInduction
open RawExact Owners.Product Owners.Provider

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)

include H

theorem partial_ambient_extension {V : Type v} (ι : V → M)
    (p : OrbitalPartial (G := G) ι) [Finite p.domain] :
    ∃ g : G, ∀ x : p.domain, g • ι x.val = ι (p.map x) := by
  let src : p.domain → Sigma (fun _ : Unit => M) := fun x => ⟨(),ι x.val⟩
  let dst : p.domain → Sigma (fun _ : Unit => M) := fun x => ⟨(),ι (p.map x)⟩
  have hc : ∀ x y, taggedColour S (src x) (src y) = taggedColour S (dst x) (dst y) := by
    intro x y
    obtain ⟨g,hgx,hgy⟩ := p.pair x y
    have hp := H.preserves_colours g (src x) (src y)
    simpa only [src,dst,Sigma.smul_mk,hgx,hgy] using hp.symm
  obtain ⟨g,hg⟩ := H.extends_finite_diagram src dst hc
  exact ⟨g,fun x => eq_of_heq (Sigma.mk.inj (hg x)).2⟩

omit H in
theorem finite_acl_eq_univ [Finite M] (A0 : Set M) : FiniteLift.aclSet G A0 = Set.univ := by
  ext x
  exact iff_of_true (Set.toFinite _) (Set.mem_univ x)

theorem finite_closed_witness [Finite M] (safe : Set (S.Atom () ()))
    (A0 : Set M) (nonemptyA : A0.Nonempty) :
    Witness S G safe A0 Set.univ ∧ FiniteLift.aclSet G (Set.univ : Set M) = Set.univ := by
  classical
  let aut (g : G) : OrbitalAut G M (Subtype.val : ↥(Set.univ : Set M) → M) :=
    restrictAut (ambientAut g) Set.univ (fun _ => Set.mem_univ _)
  refine ⟨⟨Set.toFinite _,fun _ _ => Set.mem_univ _,?_,?_⟩,finite_acl_eq_univ (G := G) (M := M) Set.univ⟩
  · intro p _ _
    obtain ⟨g,hg⟩ := partial_ambient_extension S H Subtype.val p
    refine ⟨aut g,?_⟩
    intro x
    apply Subtype.ext
    exact hg x
  · intro Z _ z _
    obtain ⟨a,ha⟩ := nonemptyA
    obtain ⟨g,hg⟩ := S.original_sort_transitive_of_homogeneous H () z.val a
    refine ⟨aut g,?_,?_⟩
    · intro x _
      rw [finite_acl_eq_univ (G := G) (M := M) A0]
      exact Set.mem_univ _
    · change g • z.val ∈ A0
      exact hg ▸ ha

theorem finite_closed_rooted [Finite M] : ClosedRooted S G := by
  intro safe _ A0 _ nonemptyA
  exact ⟨Set.univ,finite_closed_witness S H safe A0 nonemptyA⟩

end CCO.RankInduction
