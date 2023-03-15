import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime

namespace BrownCs22 
namespace Nat

def isOdd (n : ℕ) : Prop := 
  ∃ k : ℕ, n = 2 * k + 1

lemma quotient_remainder {a b c : ℕ} (h : a % b = c) : ∃ q, a = q*b + c := by 
  use a/b
  rw [← h, mul_comm, Nat.div_add_mod]


end Nat


lemma Set.inter_union_cancel_left {α : Type u} {s t : Set α} : 
  (s ∩ t) ∪ s = s := by simp

lemma Set.inter_union_cancel_right {α : Type u} {s t : Set α} : 
  (s ∩ t) ∪ t = t := by simp

namespace Int

-- def ModEq (n a b : ℤ) : Prop := n ∣ a - b




-- notation:50 a " ≡ " b " [ZMOD " n "]" => Int.ModEq n a b

end Int

def totient (n : ℕ) : ℕ := ((List.range n).filter n.coprime).length


end BrownCs22

