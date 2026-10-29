import CCO.SafeReadings.TransversalCCO
import Mathlib.Tactic.FinCases

universe v w t
namespace CCO.HKNReservoir
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds OwnerTransversal
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R))

/-- A genuine nonthin named pair belongs to the literal palette of the
INTERNALLY constructed U owner fibres. This uses its actual age embedding. -/
theorem named_pair_palette {b c : ↥B} (a : S.Atom () ())
    (x y : NamedCarrier S H R B)
    (hx : TransversalAge.ownerLabel S H R B x = b) (hy : TransversalAge.ownerLabel S H R B y = c)
    (ha : col S x.val y.val = some a)
    (hn : SafeReadings.TransversalSource.Nonthin S H a) :
    ∃ p : SafeReadings.TransversalSource.Palette S H R B b c, p.val = a := by
  let points : Fin 2 → NamedCarrier S H R B := ![x,y]
  have hsep : ∀ i j, i ≠ j → ¬ finitePacket S H (points i).val (points j).val := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact hn x.val y.val ha
    · exact fun hf => hn x.val y.val ha ((finitePacket S H).val.symm hf)
    · exact False.elim (hij rfl)
  obtain ⟨e,ho,hc⟩ := TransversalAge.embed_origins S H R B points hsep
  let u : SafeReadings.TransversalSource.Carrier S H R B b := ⟨e 0,(ho 0).trans hx⟩
  let z : SafeReadings.TransversalSource.Carrier S H R B c := ⟨e 1,(ho 1).trans hy⟩
  exact ⟨⟨a,hn,u,z,(hc 0 1).trans ha⟩,rfl⟩

end
end CCO.HKNReservoir
