import CCO.StrongExact.CycleCompletion

/-!
# Preserve one actual diversity pair during SAP injectivization

The starting diagram homomorphism already realizes the chosen endpoint
atom. Its two actual images are therefore distinct. Pinning this literal
pair while splitting other collisions retains that same atom.
-/

universe u v w z
namespace CCO.DiagramHom
variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u,v,w} ι X} {V : Type z}
variable {D : PartialDiagram S V}

/-- An actual homomorphism realizing a prescribed pair atom can be made
injective while retaining that same actual endpoint atom. -/
theorem strongCompletion_preserves_pair_of_SAP
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (f : DiagramHom D) (x y : V)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y))
    (ha : S.colour (f.point x) (f.point y) = some a) :
    ∃ g : DiagramHom D, g.IsInjective ∧
      S.colour (g.point x) (g.point y) = some a := by
  classical
  have hImages : f.image x ≠ f.image y := S.atomRel_ne ha
  have hPin : ∀ p ∈ ({x,y} : Set V), ∀ q ∈ ({x,y} : Set V),
      f.image p = f.image q → p = q := by
    intro p hp q hq hEq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · rfl
    · exact False.elim (hImages hEq)
    · exact False.elim (hImages hEq.symm)
    · rfl
  obtain ⟨g,hg,hKeep⟩ :=
    D.strongCompletion_fixed_base_of_SAP H sap f {x,y} hPin
  have hx : g.point x = f.point x := by
    have hTag := hKeep x (by simp)
    exact eq_of_heq (Sigma.mk.inj hTag).2
  have hy : g.point y = f.point y := by
    have hTag := hKeep y (by simp)
    exact eq_of_heq (Sigma.mk.inj hTag).2
  exact ⟨g,hg,by rw [hx,hy]; exact ha⟩

end CCO.DiagramHom
