import ArkLib.Data.CodingTheory.RelativeHammingDistance

section MockLinearCode

variable {F : Type*} [Semiring F]
         {ι : Type*}

/--
MOCK DEF
The set of codewords in the linear code LC within relative Hamming
distance δ of a received function f : ι → F.
-/
def list (LC : LinearCode ι F) (f : ι → F) (δ : ℚ) : Set (ι → F) := sorry

/--
MOCK DEF
A linear code LC is (δ, ℓ)–list decodable if every received word f
has at most ℓ codewords within relative Hamming distance δ.
We convert our Set to a Finset and compare .card against ℓ.
-/
def listDecodable (LC : LinearCode ι F) (δ : ℚ) (ℓ : ℕ) : Prop := sorry


end MockLinearCode
