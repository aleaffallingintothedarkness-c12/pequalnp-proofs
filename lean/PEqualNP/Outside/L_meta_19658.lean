import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19658

def witness : Circuit :=
  ⟨[⟨.or, [5, 6]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [1, 5]⟩, ⟨.not, [12]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [11, 6]⟩, ⟨.and, [16, 12]⟩, ⟨.and, [14, 15]⟩, ⟨.or, [18, 17]⟩], 19⟩

def acceptedOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or | .not => true
  | _ => false

theorem acceptedOpSound (g : Gate) (ok : acceptedOp g = true) :
    g.op = .and ∨ g.op = .or ∨ g.op = .not := by
  cases h : g.op <;> simp [acceptedOp, h] at ok ⊢

theorem witnessFit : FanInTwo witness := by
  have legal : witness.gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2)) = true := by
    decide +kernel
  intro g hg
  have passed := List.all_eq_true.mp legal g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using acceptedOpSound g passed.1,
    passed.2⟩

end PEqualNP.Outside.L_meta_19658

open PEqualNP.Outside.L_meta_19658 in
theorem PEqualNP.Outside.L_meta_19658 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (15762641 : ℕ).testBit (5 * u.val + v.val)) C) := by
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
