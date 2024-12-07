import Batteries
import Aoc
import Aoc.Lib.List

open Std

def part1 (xs : List Nat) (ys : List Nat) : Nat :=
  match xs, ys with
  | x::xs, y::ys => (if x < y then y - x else x - y) + part1 xs ys
  | _, _ => 0

def part2 (xs : List Nat) (ys : List Nat) : Nat :=
  let map := ys.foldl (λ acc x ↦ acc.alter x (λ op ↦
    (op.map (λ n ↦ n + 1)).or (some 1)
  )) HashMap.empty
  xs.foldl (fun acc x => acc + (map.getD x 0) * x) 0

def main : IO Unit := IO.interact $ λ input ↦
  let (fst, snd) := lines input
    |> List.map (List.first2 ∘ List.map String.toNat! ∘ words)
    |> List.unzip

  s!"{part1 fst.mergeSort snd.mergeSort}\n{part2 fst snd}"
