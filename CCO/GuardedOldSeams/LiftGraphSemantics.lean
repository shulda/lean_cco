import CCO.GuardedOldSeams.LiftGraphTheta
import CCO.Injectivization

/-! The actual finite root/private-theta union has precisely the specified
positive-word root-menu semantics. Visible SAP makes the whole graph
injective while fixing every already-injective old root. No CCO or hidden
completion provider is used in this equivalence. -/

universe u v a p q t

namespace CCO.GuardedOldSeams

open StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,a} ι X)
variable {P : Type p} {K : Type q} [Finite P] [Finite K]

namespace RootWordSystem

variable {S} (R : RootWordSystem S P K)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)

/-- Every individual package is seeded from an actual common fine atom.
The choices are local to that package and do not presume global roots. -/
noncomputable def seedsOfNonemptyPresent
    (survivor : ∀ k, (present S (R.words k)).Nonempty) : RootWordSeeds S R := by
  classical
  let atom k := Classical.choose (survivor k)
  have ha k : atom k ∈ present S (R.words k) := Classical.choose_spec (survivor k)
  let x k := Classical.choose (S.realized (atom k))
  let y k := Classical.choose (Classical.choose_spec (S.realized (atom k)))
  have hxy k : S.colour (x k) (y k) = some (atom k) :=
    Classical.choose_spec (Classical.choose_spec (S.realized (atom k)))
  refine ⟨x,y,fun k b => LiteralLine.of_represented S ((R.words k).get b) (x k) (y k) ?_⟩
  exact profile_realizes_prescribed_pair_of_SAP S H sap _ (atom k)
    (ha k _ (List.get_mem _ b)) _ _ (hxy k)

structure RootRealization where
  point : ∀ p, X (R.sort p)
  injective : Function.Injective (fun p => (⟨R.sort p,point p⟩ : Sigma X))
  profile : ∀ k, S.menuRel (present S (R.words k)) (point (R.left k)) (point (R.right k))

variable (seed : RootWordSeeds S R)

/-- Read every whole original word from the actual restricted theta. -/
theorem hom_represented_word (f : DiagramHom (R.diagram seed)) (k : K)
    (word : PositiveWord S (R.sort (R.left k)) (R.sort (R.right k)))
    (hword : word ∈ R.words k) :
    PositiveWord.represented S word (f.point (.inl (R.left k)))
      (f.point (.inl (R.right k))) := by
  have hw := thetaEdgesOfLiteralLines_representsWords S (R.words k)
    (seed.left k) (seed.right k) (seed.lines k) (R.restrictTheta seed f k) word hword
  exact hw

/-- Injective graph roots have the actual fine endpoint atom in every
one of the package's specified original word profiles. -/
noncomputable def rootsOfInjectiveHom (f : DiagramHom (R.diagram seed))
    (hf : f.IsInjective) : R.RootRealization where
  point p := f.point (.inl p)
  injective := by
    intro p q hpq
    exact Sum.inl.inj (hf hpq)
  profile k := by
    have hne : f.image (.inl (R.left k)) ≠ f.image (.inl (R.right k)) := by
      intro heq
      exact R.left_ne_right k (Sum.inl.inj (hf heq))
    obtain ⟨b,hb⟩ := S.some_colour_of_ne (f.point (.inl (R.left k)))
      (f.point (.inl (R.right k))) hne
    refine ⟨b,?_,hb⟩
    intro word hw
    exact (positive_profile_iff_represented S H sap word b).mpr
      ⟨_,_,R.hom_represented_word seed f k word hw,hb⟩

/-- Actual prescribed-root source walks give an ordinary union graph
homomorphism, before any appeal to SAP freshness. -/
noncomputable def homOfRootRealization (root : R.RootRealization) :
    DiagramHom (R.diagram seed) := by
  classical
  let lines : ∀ k b, LiteralLine S ((R.words k).get b)
      (root.point (R.left k)) (root.point (R.right k)) := fun k b =>
    LiteralLine.of_represented S _ _ _ (by
      obtain ⟨atom,ha,hxy⟩ := root.profile k
      exact profile_realizes_prescribed_pair_of_SAP S H sap _ atom
        (ha _ (List.get_mem _ b)) _ _ hxy)
  exact R.homOfLines seed root.point lines

include H sap

/-- The literal old roots are unchanged when the whole private union is
made injective. All other graph vertices are genuine private positions. -/
theorem injective_hom_of_root_realization (root : R.RootRealization) :
    ∃ f : DiagramHom (R.diagram seed), f.IsInjective ∧
      ∀ p, f.point (.inl p) = root.point p := by
  classical
  let f₀ := R.homOfRootRealization H sap seed root
  let pins : Set R.Vertex := Set.range (fun p : P => (Sum.inl p : R.Vertex))
  have hPin : ∀ x ∈ pins, ∀ y ∈ pins, f₀.image x = f₀.image y → x = y := by
    rintro x ⟨p,rfl⟩ y ⟨q,rfl⟩ heq
    exact congrArg Sum.inl (root.injective heq)
  obtain ⟨f,hf,hfixed,_⟩ := DiagramHom.injectivize_of_SAP H sap f₀ pins hPin
    ∅ Set.finite_empty
  refine ⟨f,hf,?_⟩
  intro p
  have hp := hfixed (.inl p) ⟨p,rfl⟩
  change f.point (.inl p) = f₀.point (.inl p)
  simpa only [DiagramHom.image,Sigma.mk.injEq,heq_eq_eq,true_and] using hp

theorem strong_completion_iff_root_realization :
    (∃ f : DiagramHom (R.diagram seed), f.IsInjective) ↔ Nonempty R.RootRealization := by
  constructor
  · rintro ⟨f,hf⟩
    exact ⟨R.rootsOfInjectiveHom H sap seed f hf⟩
  · rintro ⟨root⟩
    obtain ⟨f,hf,_⟩ := R.injective_hom_of_root_realization H sap seed root
    exact ⟨f,hf⟩

/-- Ordinary homomorphic realization has the same root semantics because
the source's proved SAP injectivisation separates the finite graph. -/
theorem hom_iff_root_realization :
    Nonempty (DiagramHom (R.diagram seed)) ↔ Nonempty R.RootRealization := by
  constructor
  · rintro ⟨f⟩
    obtain ⟨g,hg,_,_⟩ := DiagramHom.injectivize_of_SAP H sap f ∅
      (by simp) ∅ Set.finite_empty
    exact ⟨R.rootsOfInjectiveHom H sap seed g hg⟩
  · rintro ⟨root⟩
    exact ⟨R.homOfRootRealization H sap seed root⟩

end RootWordSystem
end CCO.GuardedOldSeams
