import CCO.OrbitalCover.Example.SAP
import CCO.OrbitalCover.Example.Prescribed
import CCO.APCharacter.Rank.Source
import CCO.StrongExact.TriangleFullness

/-! The chosen global phase predicates, first p and then (p,q), as literal
named-sort refinements of the same original carrier. Palettes contain only
old colours which actually occur between the named children. -/
universe z
namespace CCO.OrbitalCover.Example
namespace Prefix

inductive Stage | first | both
  deriving DecidableEq

def Label : Stage → Type
  | .first => Bit
  | .both => Bit × Bit
instance (k : Stage) : Fintype (Label k) := by cases k <;> dsimp [Label] <;> infer_instance
instance (k : Stage) : DecidableEq (Label k) := by cases k <;> dsimp [Label] <;> infer_instance

def mark : (k : Stage) → Point → Label k
  | .first, x => x.p
  | .both, x => (x.p, x.q)

abbrev β (k : Stage) (_ : Unit) := Label k
abbrev child (k : Stage) := APCharacter.Rank.Child (β k)
abbrev carrier (k : Stage) := APCharacter.Rank.Point (β k) (fun _ => mark k)

theorem inhabited (k : Stage) (c : child k) : Nonempty (carrier k c) := by
  rcases c with ⟨i,b⟩
  cases i
  cases k with
  | first => exact ⟨⟨⟨0,0,b,0,0⟩,rfl⟩⟩
  | both => exact ⟨⟨⟨0,0,b.1,b.2,0⟩,rfl⟩⟩

noncomputable def source (k : Stage) : AtomicSource (child k) (carrier k) :=
  APCharacter.Rank.source Example.source (β k) (fun _ => mark k) (inhabited k)

def erase (k : Stage) (x : Sigma (carrier k)) : Point := x.2.val

theorem erase_injective (k : Stage) : Function.Injective (erase k) := by
  intro x y h
  apply APCharacter.Rank.forget_injective (β k) (fun _ => mark k)
  exact Sigma.ext (Subsingleton.elim _ _) (heq_of_eq h)

def oldEquiv (k : Stage) : Sigma (carrier k) ≃ Point where
  toFun := erase k
  invFun x := ⟨⟨(),mark k x⟩,⟨x,rfl⟩⟩
  left_inv := by intro x; apply erase_injective k; rfl
  right_inv := by intro x; rfl

theorem colour_map (k : Stage) {c d : child k} (x : carrier k c) (y : carrier k d) :
    ((source k).colour x y).map Subtype.val = colour x.val y.val :=
  APCharacter.Rank.colour_map Example.source (β k) (fun _ => mark k) x y

theorem colour_some (k : Stage) {c d : child k} (x : carrier k c) (y : carrier k d)
    (a : (source k).Atom c d) :
    (source k).colour x y = some a ↔ colour x.val y.val = some a.val :=
  APCharacter.Rank.colour_some_iff Example.source (β k) (fun _ => mark k) x y a

theorem finite_extension (k : Stage) {V : Type*} [Finite V] (f h : V → Point)
    (hc : ∀ v w, colour (f v) (f w) = colour (h v) (h w))
    (hm : ∀ v, mark k (f v) = mark k (h v)) :
    ∃ g : Aut, (∀ v, g • f v = h v) ∧ ∀ x, mark k (g • x) = mark k x := by
  cases k with
  | first =>
    obtain ⟨g,hg,hp,_⟩ := finite_extension_controlled f h hc true false
      (fun _ => hm) (fun h => Bool.noConfusion h)
    exact ⟨g,hg,hp rfl⟩
  | both =>
    obtain ⟨g,hg,hp,hq⟩ := finite_extension_controlled f h hc true true
      (fun _ v => congrArg Prod.fst (hm v)) (fun _ v => congrArg Prod.snd (hm v))
    exact ⟨g,hg,fun x => Prod.ext (hp rfl x) (hq rfl x)⟩

def autGroup (k : Stage) : Subgroup Aut where
  carrier := {g | ∀ x, mark k (g • x) = mark k x}
  one_mem' := by intro x; rfl
  mul_mem' := by intro g h hg hh x; exact (hg (h • x)).trans (hh x)
  inv_mem' := by
    intro g hg x
    have hh := hg (g⁻¹ • x)
    simpa using hh.symm
abbrev FullGroup (k : Stage) := autGroup k

instance (k : Stage) (c : child k) : MulAction (FullGroup k) (carrier k c) where
  smul g x := ⟨g.val • x.val, (g.property x.val).trans x.property⟩
  one_smul x := by apply Subtype.ext; exact one_smul Aut x.val
  mul_smul g h x := by apply Subtype.ext; exact mul_smul g.val h.val x.val

theorem action_colours (k : Stage) (g : FullGroup k) (p q : Sigma (carrier k)) :
    taggedColour (source k) (g • p) (g • q) = taggedColour (source k) p q := by
  rcases p with ⟨c,x⟩
  rcases q with ⟨d,y⟩
  change (⟨c,d,(source k).colour (g • x) (g • y)⟩ : Σ c, Σ d, Option ((source k).Atom c d)) =
    ⟨c,d,(source k).colour x y⟩
  apply congrArg (fun a => (⟨c,d,a⟩ : Σ c, Σ d, Option ((source k).Atom c d)))
  apply Option.map_injective Subtype.val_injective
  rw [colour_map,colour_map]
  exact aut_colour g.val x.val y.val

theorem homogeneous (k : Stage) : HomogeneousSource (source k) (FullGroup k) where
  preserves_sort := by intro g p; cases p; rfl
  preserves_colours := action_colours k
  extends_finite_diagram := by
    intro V _ f h hc
    have hs (v : V) : (f v).1 = (h v).1 :=
      congrArg (fun a : Σ c, Σ d, Option ((source k).Atom c d) => a.1) (hc v v)
    have hm (v : V) : mark k (erase k (f v)) = mark k (erase k (h v)) :=
      (f v).2.property.trans ((congrArg Sigma.snd (hs v)).trans (h v).2.property.symm)
    have hcol : ∀ v w, colour (erase k (f v)) (erase k (f w)) =
        colour (erase k (h v)) (erase k (h w)) := by
      intro v w
      have hh := hc v w
      let read : (Σ c, Σ d, Option ((source k).Atom c d)) → Option Colour :=
        fun a => a.2.2.map Subtype.val
      have he := congrArg read hh
      exact (colour_map k (f v).2 (f w).2).symm.trans
        (he.trans (colour_map k (h v).2 (h w).2))
    obtain ⟨g,hg,hmark⟩ := finite_extension k (fun v => erase k (f v)) (fun v => erase k (h v)) hcol hm
    refine ⟨⟨g,hmark⟩,fun v => ?_⟩
    apply erase_injective k
    exact hg v

end Prefix
end CCO.OrbitalCover.Example
