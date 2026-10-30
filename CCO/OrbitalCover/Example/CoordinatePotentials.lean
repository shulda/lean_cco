import CCO.OrbitalCover.Example.Potentials
import CCO.OrbitalCover.Example.Bits

/-! One block coordinate and its optional two-valued gain are solved from
actual original simple cycles. This applies equally to unnamed or prescribed
endpoint phases and will be instantiated independently in both coordinates. -/
universe u v w z
namespace CCO.OrbitalCover.Example.Potentials
open CCO.RealClosure.Bounds.Examples.CycleConsistency
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {V : Type z} (D : PartialDiagram S V)

theorem coordinate_blocks (read : ∀ {i j}, S.Atom i j → Option (ZMod 2))
    (hsym : ∀ {i j} (a : S.Atom i j), read (S.conv a) = read a)
    (block : ∀ i, X i → ℕ) (phase : ∀ i, X i → ZMod 2)
    (hvalue : ∀ {i j} (x : X i) (y : X j) (a : S.Atom i j),
      S.colour x y = some a → read a =
        if block i x = block j y then some (phase i x + phase j y) else none)
    (hcycles : ∀ C : SimpleCycle D, CycleHom C) :
    ∃ label : V → ℕ, ∀ x y (h : x ≠ y) (a : S.Atom (D.vertexSort x) (D.vertexSort y)),
      D.edge x y h = some a → (label x = label y ↔ (read a).isSome = true) := by
  apply coordinate_labels S D (fun a => (read a).isSome) (fun a => by rw [hsym]) block
  · intro i j x y a ha
    rw [hvalue x y a ha]
    by_cases h : block i x = block j y <;> simp [h]
  · exact hcycles

theorem coordinate_solution (read : ∀ {i j}, S.Atom i j → Option (ZMod 2))
    (hsym : ∀ {i j} (a : S.Atom i j), read (S.conv a) = read a)
    (block : ∀ i, X i → ℕ) (phase : ∀ i, X i → ZMod 2)
    (hvalue : ∀ {i j} (x : X i) (y : X j) (a : S.Atom i j),
      S.colour x y = some a → read a =
        if block i x = block j y then some (phase i x + phase j y) else none)
    (hcycles : ∀ C : SimpleCycle D, CycleHom C) :
    ∃ (label : V → ℕ) (bits : V → ZMod 2),
      ∀ x y (h : x ≠ y) (a : S.Atom (D.vertexSort x) (D.vertexSort y)),
      D.edge x y h = some a → read a =
        if label x = label y then some (bits x + bits y) else none := by
  obtain ⟨label,hlabel⟩ := coordinate_blocks S D read hsym block phase hvalue hcycles
  let readBool : OptionalReader S := fun a => (read a).map bitBool
  have hreadBool : ∀ {i j} (a : S.Atom i j), readBool (S.conv a) = readBool a := by
    intro i j a
    dsimp [readBool]
    rw [hsym]
  have hv : ∀ {i j} (x : X i) (y : X j) (a : S.Atom i j) (b : Bool),
      S.colour x y = some a → readBool a = some b →
      (bitBool (phase i x) ^^ bitBool (phase j y)) = b := by
    intro i j x y a b ha hb
    change (read a).map bitBool = some b at hb
    rw [hvalue x y a ha] at hb
    by_cases hh : block i x = block j y
    · simpa only [if_pos hh,Option.map_some,Option.some.injEq,bitBool_add] using hb
    · simp only [if_neg hh,Option.map_none] at hb
      cases hb
  obtain ⟨f,hf⟩ := optional_phase_labels S D readBool hreadBool
    (fun i x => bitBool (phase i x)) hv hcycles
  refine ⟨label,fun x => boolBit (f x),?_⟩
  intro x y h a ha
  have hl := hlabel x y h a ha
  cases hr : read a with
  | none =>
    have hn : label x ≠ label y := by simpa only [hr,Option.isSome_none,Bool.false_eq_true,iff_false] using hl
    simp only [if_neg hn,hr]
  | some b =>
    have he : label x = label y := hl.mpr (by simp only [hr,Option.isSome_some])
    have hh := hf x y h a (bitBool b) ha (by change (read a).map bitBool = some (bitBool b); rw [hr]; rfl)
    rw [if_pos he]
    congr 1
    apply bitBool_injective
    simpa only [bitBool_add,bitBool_boolBit] using hh.symm

/-- If the endpoint phases are already unary labels, retain those exact
phases and solve only the block equality system. -/
theorem coordinate_prescribed (read : ∀ {i j}, S.Atom i j → Option (ZMod 2))
    (hsym : ∀ {i j} (a : S.Atom i j), read (S.conv a) = read a)
    (block : ∀ i, X i → ℕ) (phase : ∀ i, X i → ZMod 2)
    (hvalue : ∀ {i j} (x : X i) (y : X j) (a : S.Atom i j),
      S.colour x y = some a → read a =
        if block i x = block j y then some (phase i x + phase j y) else none)
    (hcycles : ∀ C : SimpleCycle D, CycleHom C)
    (bits : V → ZMod 2)
    (hbits : ∀ x y (h : x ≠ y) (a : S.Atom (D.vertexSort x) (D.vertexSort y)) (b : ZMod 2),
      D.edge x y h = some a → read a = some b → bits x + bits y = b) :
    ∃ label : V → ℕ, ∀ x y (h : x ≠ y) (a : S.Atom (D.vertexSort x) (D.vertexSort y)),
      D.edge x y h = some a → read a =
        if label x = label y then some (bits x + bits y) else none := by
  obtain ⟨label,hlabel⟩ := coordinate_blocks S D read hsym block phase hvalue hcycles
  refine ⟨label,?_⟩
  intro x y h a ha
  have hl := hlabel x y h a ha
  cases hr : read a with
  | none =>
    have hn : label x ≠ label y := by simpa only [hr,Option.isSome_none,Bool.false_eq_true,iff_false] using hl
    simp only [hr,if_neg hn]
  | some b =>
    have he : label x = label y := hl.mpr (by simp only [hr,Option.isSome_some])
    rw [if_pos he,hbits x y h a b ha hr]

end CCO.OrbitalCover.Example.Potentials
