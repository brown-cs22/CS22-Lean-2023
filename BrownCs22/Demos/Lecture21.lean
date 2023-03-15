import BrownCs22.Library.Defs
import BrownCs22.Library.Tactics 
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Int.GCD

open BrownCs22


/-  

Let's check computationally that our RSA algorithm works.

-/

-- given a public key and a modulus `n`, we can encrypt a message.
def rsa_encrypt (public_key : ℕ) (n : ℕ) (message : ℕ) : ℕ :=
  (message ^ public_key) % n 

-- given a private key and a modulus `n`, we can decrypt a message.
def rsa_decrypt (private_key : ℕ) (n : ℕ) (encrypted_message : ℕ) : ℕ :=
  (encrypted_message ^ private_key) % n



-- let's choose `n` to be the product of two primes.
def p := 113
def q := 37 
def n := p * q

#eval Nat.Prime p
#eval Nat.Prime q

-- We choose our public key that is relatively prime to `(p - 1)*(q - 1)`.
def public_key := 13

#eval Nat.gcd public_key ((p - 1)*(q - 1))


-- Now we need an inverse to the public key mod `(p - 1)*(q - 1)`.
-- We get this from the extended Euclidean algorithm.
#eval Nat.xgcd public_key ((p - 1)*(q - 1))

def private_key := 1861 

-- double check it's an inverse
#eval private_key * public_key  % ((p - 1)*(q - 1))




-- Okay! Let's choose a message.
def message := 1034

def encrypted_message := rsa_encrypt public_key n message 

#eval encrypted_message 


def decrypted_message := rsa_decrypt private_key n encrypted_message 

-- encrypting and decrypting the message produces the same output!
#eval decrypted_message 




-- We can state, and (mostly) prove, the partial correctness theorem from class!
theorem rsa_correct 
  (p q : ℕ) (public_key private_key : ℕ) (message : ℕ)
  (hp : Prime p) (hq : Prime q)
  (h_pub_pri : public_key * private_key ≡ 1 [MOD (p - 1)*(q - 1)])
  (h_msg : message < p*q)
  (h_rel_prime : Nat.gcd msg (p*q) = 1) : 

    rsa_decrypt private_key (p*q) 
      (rsa_encrypt public_key (p*q) message)
        = message :=
  by 
  dsimp [rsa_decrypt, rsa_encrypt]

  have h_lin_combo : ∃ k, public_key * private_key = 1 + (p - 1)*(q - 1)*k := 
    sorry

  eliminate h_lin_combo with k hk

  calc 
    (message ^ public_key % (p * q)) ^ private_key % (p * q) 
      = (message ^ public_key) ^ private_key % (p * q)      := by rw [← Nat.pow_mod]
    _ = message ^ (public_key * private_key) % (p * q)      := by rw [pow_mul] 
    _ = message ^ (1 + (p - 1)*(q - 1)*k) % (p * q)         := by rw [hk]
    _ = message ^ (1 + totient (p*q)*k) % (p * q)           := by sorry 
    _ = (message * (message ^ totient (p * q))^k) % (p * q) := by rw [pow_add, pow_one, pow_mul]
    _ = (message % (p * q)) * ((message ^ totient (p * q))^k % (p * q)) % (p * q) 
                                                            := by rw [Nat.mul_mod]
    _ = (message % (p * q)) * 1 % (p * q)                   := by sorry 
    _ = message % (p * q)                                   := by rw [mul_one, Nat.mod_mod]
    _ = message                                             := by rw [Nat.mod_eq_of_lt h_msg]
