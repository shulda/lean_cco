import CCO.FiniteKernel.LocalGroups

/-!
# Binary patching on all actual points

The global kernel is identified with the actual local-pair CSP by a group
isomorphism, not by an assumed reconstruction provider. Unary predicates,
within-fibre loops, both directed cross orientations and empty universes are
covered. Neither countability nor any homogeneity hypothesis is used.
-/

universe u v w z
namespace CCO.FiniteKernel.FinitePartition
noncomputable section
variable {X : Type u} {S : BinaryStructure.{u,v,w} X} {I : Type z}
variable (P : FinitePartition S I)

def fibrePerm (g : P.kernel) (i : I) : Equiv.Perm (P.Fibre i) where
  toFun x := ⟨g.val.val x.val,(P.kernel_fixes g x.val).trans x.property⟩
  invFun x := ⟨(g⁻¹).val.val x.val,(P.kernel_fixes g⁻¹ x.val).trans x.property⟩
  left_inv := by
    intro x
    apply Subtype.ext
    exact g.val.val.symm_apply_apply x.val
  right_inv := by
    intro x
    apply Subtype.ext
    exact g.val.val.apply_symm_apply x.val

def restrictFibre (i : I) : P.kernel →* P.Intrinsic i where
  toFun g := ⟨P.fibrePerm g i,
    ⟨fun r x => g.val.property.1 r x.val,
      fun r x y => g.val.property.2 r x.val y.val⟩⟩
  map_one' := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    apply Subtype.ext
    rfl
  map_mul' g h := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    apply Subtype.ext
    rfl

def rho : P.kernel →* (∀ i, P.Intrinsic i) where
  toFun g i := P.restrictFibre i g
  map_one' := by funext i; exact (P.restrictFibre i).map_one
  map_mul' g h := by funext i; exact (P.restrictFibre i).map_mul g h

theorem rho_injective : Function.Injective P.rho := by
  intro g h heq
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro x
  exact congrArg (fun p : ∀ i, P.Intrinsic i =>
    ((p (P.owner x)).val ⟨x,rfl⟩).val) heq

theorem rho_mem (g : P.kernel) : P.rho g ∈ P.globalSolutions := by
  intro i j _
  exact ⟨fun r x y => g.val.property.2 r x.val y.val,
    fun r y x => g.val.property.2 r y.val x.val⟩

/-- Assemble the original real-point bijection via the canonical partition
equivalence. The components are actual induced automorphisms. -/
def assemble (p : ∀ i, P.Intrinsic i) : Equiv.Perm X :=
  P.split.trans ((Equiv.sigmaCongrRight fun i => (p i).val).trans P.split.symm)

theorem assemble_on_fibre (p : ∀ i, P.Intrinsic i) (i : I) (x : P.Fibre i) :
    P.assemble p x.val = ((p i).val x).val := by
  rcases x with ⟨x,hx⟩
  dsimp [assemble,split]
  cases hx
  rfl

theorem assemble_owner (p : ∀ i, P.Intrinsic i) (x : X) :
    P.owner (P.assemble p x) = P.owner x := by
  rw [P.assemble_on_fibre p (P.owner x) ⟨x,rfl⟩]
  exact ((p (P.owner x)).val ⟨x,rfl⟩).property

theorem assemble_preserves (p : ∀ i, P.Intrinsic i) (hp : p ∈ P.globalSolutions) :
    P.assemble p ∈ S.autGroup := by
  constructor
  · intro r x
    rw [P.assemble_on_fibre p (P.owner x) ⟨x,rfl⟩]
    exact (p (P.owner x)).property.1 r ⟨x,rfl⟩
  · intro r x y
    by_cases hxy : P.owner x = P.owner y
    · let xx : P.Fibre (P.owner x) := ⟨x,rfl⟩
      let yy : P.Fibre (P.owner x) := ⟨y,hxy.symm⟩
      rw [P.assemble_on_fibre p (P.owner x) xx,P.assemble_on_fibre p (P.owner x) yy]
      exact (p (P.owner x)).property.2 r xx yy
    · let xx : P.Fibre (P.owner x) := ⟨x,rfl⟩
      let yy : P.Fibre (P.owner y) := ⟨y,rfl⟩
      rw [P.assemble_on_fibre p (P.owner x) xx,P.assemble_on_fibre p (P.owner y) yy]
      exact (hp (P.owner x) (P.owner y) hxy).1 r xx yy

def assembleKernel (p : P.globalSolutions) : P.kernel :=
  ⟨⟨P.assemble p.val,P.assemble_preserves p.val p.property⟩,
    (P.mem_kernel_iff _).mpr (P.assemble_owner p.val)⟩

theorem rho_assemble (p : P.globalSolutions) : P.rho (P.assembleKernel p) = p.val := by
  funext i
  apply Subtype.ext
  apply Equiv.ext
  intro x
  apply Subtype.ext
  exact P.assemble_on_fibre p.val i x

/-- C04: the actual full owner kernel is EXACTLY the entire local pair CSP.
This is an isomorphism of actual groups, including the empty product. -/
def kernelIso : P.kernel ≃* P.globalSolutions where
  toFun g := ⟨P.rho g,P.rho_mem g⟩
  invFun := P.assembleKernel
  left_inv g := P.rho_injective (P.rho_assemble ⟨P.rho g,P.rho_mem g⟩)
  right_inv p := Subtype.ext (P.rho_assemble p)
  map_mul' _ _ := Subtype.ext (P.rho.map_mul _ _)

theorem mem_range_rho (p : ∀ i, P.Intrinsic i) :
    p ∈ Set.range P.rho ↔ p ∈ P.globalSolutions := by
  constructor
  · rintro ⟨g,rfl⟩
    exact P.rho_mem g
  · intro hp
    exact ⟨P.assembleKernel ⟨p,hp⟩,P.rho_assemble ⟨p,hp⟩⟩

end
end CCO.FiniteKernel.FinitePartition
