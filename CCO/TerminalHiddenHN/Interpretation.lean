import CCO.TerminalHiddenHN.EquivariantFunctions
import CCO.UnaryFreshFrames.Quotient.Named
import CCO.TerminalHiddenHN.BinaryCodec

/-! The structural data of a finite binary equivariant unary
interpretation on the original real sorts. These are the literal A02
inputs to standalone cofinality and readout: no SAP, CCO, terminal-cover,
hidden amalgamation or Ramsey hypothesis is part of this interface.
The actual MI interpretation will separately instantiate these data.
-/

universe u v w r l k
namespace CCO.TerminalHiddenHN

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]

structure RealInterpretation
    (U : CCO.UnaryFreshFrames.Language.{max u l})
    {V : Type k} (P : CCO.UnaryFreshFrames.Structure U V) where
  finiteSorts : Finite U.Sorts
  finiteFuncs : Finite U.Func
  finiteRels : Finite U.Rel
  binary : ∀ R, U.arity R = 2
  realSort : ι ↪ U.Sorts
  root : ∀ i, X i → P.Carrier (realSort i)
  root_bijective : ∀ i, Function.Bijective (root i)
  motion : G →* P.Aut
  root_equivariant : ∀ (g : G) i (x : X i),
    (motion g) • (root i x).val = (root i (g • x)).val
  /-- A primitive with real output is only the identity. This also
  allows harmless named identities; it excludes every real selector. -/
  primitive_real_identity : ∀ F i, U.output F = realSort i → ∀ x, P.func F x = x
  /-- Each hidden sort has one genuine onto real-source projection
  term. It is uniform on that sort and creates no point in a finite host. -/
  projection : ∀ s : U.Sorts, ∃ i,
    ∃ q : CCO.UnaryFreshFrames.Term U (realSort i) s,
      Function.Surjective (fun x => P.typedEval q (root i x))
  atom : ∀ {i j}, S.Atom i j → U.Rel
  atom_iff : ∀ {i j} (a : S.Atom i j) (x : X i) (y : X j),
    P.rel (atom a)
      (fun n => if n.val = 0 then (root i x).val else (root j y).val) ↔
      S.atomRel a x y

namespace RealInterpretation
variable {S}
variable {U : CCO.UnaryFreshFrames.Language.{max u l}} {V : Type k}
variable {P : CCO.UnaryFreshFrames.Structure U V}
variable (D : RealInterpretation (G := G) S U P)

def realPoint (p : Sigma X) : V := (D.root p.1 p.2).val

theorem sort_realPoint (p : Sigma X) : P.sort (D.realPoint p) = D.realSort p.1 :=
  (D.root p.1 p.2).property

theorem realPoint_injective : Function.Injective D.realPoint := by
  rintro ⟨i,x⟩ ⟨j,y⟩ h
  have hs : D.realSort i = D.realSort j :=
    (D.sort_realPoint ⟨i,x⟩).symm.trans
      ((congrArg P.sort h).trans (D.sort_realPoint ⟨j,y⟩))
  have hij := D.realSort.injective hs
  subst j
  have he : D.root i x = D.root i y := Subtype.ext h
  have hxy := (D.root_bijective i).1 he
  cases hxy
  rfl

theorem realPoint_smul (g : G) (p : Sigma X) :
    D.realPoint (g • p) = (D.motion g) • D.realPoint p := by
  cases p with
  | mk i x => exact (D.root_equivariant g i x).symm

theorem realPoint_surjective_on_sort (i : ι) (x : V)
    (hx : P.sort x = D.realSort i) : ∃ a : X i, D.realPoint ⟨i,a⟩ = x := by
  obtain ⟨a,ha⟩ := (D.root_bijective i).2 ⟨x,hx⟩
  exact ⟨a,congrArg Subtype.val ha⟩

noncomputable def signature : CCO.UnarySupport.Signature.{max u l} := by
  letI := D.finiteSorts
  letI := D.finiteFuncs
  letI := D.finiteRels
  exact CCO.HiddenSAPReadings.partialSignature U

noncomputable def partialModel : CCO.UnarySupport.Structure D.signature V := by
  letI := D.finiteSorts
  letI := D.finiteFuncs
  letI := D.finiteRels
  exact CCO.HiddenSAPReadings.partialTarget P

abbrev codeLanguage : CCO.FullCode.Language.{max u l} :=
  binaryLanguage D.signature D.binary

noncomputable def codeModel : CCO.FullCode.Structure D.codeLanguage V :=
  binaryStructure D.signature D.binary D.partialModel

end RealInterpretation

end CCO.TerminalHiddenHN
