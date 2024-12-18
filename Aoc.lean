import Aoc.Lib.IO

-- Basic Helpers

def lines (s : String) : List String := s.splitOn "\n" |>.reverse |>.dropWhile String.isEmpty |>.reverse
def words (s : String) : List String := s.split Char.isWhitespace |>.filter (not ∘ String.isEmpty)

def unlines : List String → String := .intercalate "\n"

def uncurry (f : α → β → γ) : (α × β → γ) | (a, b) => f a b
