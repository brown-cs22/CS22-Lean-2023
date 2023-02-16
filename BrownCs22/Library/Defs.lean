import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime

namespace BrownCs22 
namespace Nat

def isOdd (n : ℕ) : Prop := 
  ∃ k : ℕ, n = 2 * k + 1

end Nat


lemma Set.inter_union_cancel_left {α : Type u} {s t : Set α} : 
  (s ∩ t) ∪ s = s := by simp

lemma Set.inter_union_cancel_right {α : Type u} {s t : Set α} : 
  (s ∩ t) ∪ t = t := by simp


end BrownCs22

