import Batteries
import Aoc
import Aoc.Lib.List

open Std

def charListToNat (xs: List Char) : Nat :=
  let str := xs.foldl (λ acc x => acc.push x) ""
  str.toNat!

def drop (digits: List Char) (n: Nat) :=
  let rec drop_h digits n acc :=
    match n, digits with
    | 0, xs => (acc.reverse, xs)
    | a + 1, x :: xs => drop_h xs a (x :: acc)
    | _ + 1, [] => (acc.reverse, [])
  let (fst, snd) := drop_h digits n []
  ((charListToNat fst), (charListToNat snd))

def even_digits_split (a: Nat) : Option (Nat × Nat) :=
  let digits := (Nat.toDigits 10 a)
  if digits.length % 2 == 0
  then
    some (drop digits (digits.length / 2))
  else
    none

def step  (xs: List Nat) (acc: List Nat) : List Nat :=
  match xs with
  | 0 :: xs => step xs (1 :: acc)
  | a :: xs =>
    match even_digits_split a with
    | none => step xs (a * 2024 :: acc)
    | some (a, b) => step xs (b :: a :: acc)
  | [] => acc.reverse

def stepN : List Nat → Nat → List Nat
  | xs, 0 =>  xs
  | xs, n + 1 =>
    let _ := println! "stepN {n}"
    (stepN (step xs []) n)

def main : IO Unit := IO.interact $ λ input ↦
  let input:= lines input
    |>.map (List.map String.toNat! ∘ words)
    |>.head!

  let part1 := stepN input 75

  s! "{part1.length}"
