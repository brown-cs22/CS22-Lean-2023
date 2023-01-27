import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime

namespace BrownCs22 
namespace Nat

def isOdd (n : ℕ) : Prop := 
  ∃ k : ℕ, n = 2 * k + 1

end Nat
end BrownCs22