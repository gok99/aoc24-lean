import Batteries
import Aoc
import Aoc.Lib.List

open Std

def extractOrd (lines : List String) (acc : List String) :=
  match lines with
  | "" :: rest => (acc, rest)
  | l :: rest => extractOrd rest (l :: acc)
  | _ => (acc, [])

def part1 (hm: HashMap Nat (HashSet Nat)) (mid: Nat) (s: List Nat) : Nat :=
  match s with
  | n :: rest => if rest.all (fun x => (hm.getD n HashSet.empty).contains x)
    then (part1 hm mid rest)
    else 0
  | [] => mid

def listEquals (xs: List Nat) (ys: List Nat) :=
  match xs, ys with
  | x :: xs, y :: ys => x == y && listEquals xs ys
  | [], [] => true
  | _, _ => false

def part2 (hm: HashMap Nat (HashSet Nat)) (s: List Nat) : Option (List Nat) :=
  let s' := s.map (fun x => (x, s.erase x))
    |> List.map (fun (y, xs) => (List.count2 (fun x => (hm.getD y HashSet.empty).contains x) xs, y))
    |> List.mergeSort (le := fun a b => a.fst >= b.fst)
    |> List.map (fun s => s.snd)

  match listEquals s s' with
  | true => none
  | false => some s'

def main : IO Unit := IO.interact $ λ input =>
  let reports := lines input

  let (ord, seq) := extractOrd reports []

  let ord := ord |> List.map (List.first2 ∘ (List.map String.toNat!) ∘ (String.splitOn (sep := "|")))
  let seq := seq |> List.map ((List.map String.toNat!) ∘ String.splitOn (sep := ","))

  let init : HashMap Nat (HashSet Nat) := HashMap.empty

  let orderMap1 := List.foldl (fun map (l, r) => map.alter l (fun v =>
    (match v with
    | some e => HashSet.insert e r
    | none => HashSet.empty.insert r)
  )) init ord

  let part1_res := List.map (fun s => part1 orderMap1 (s[s.length / 2]!) s) seq |> List.sum
  let part2_res := List.map (fun s =>
    part2 orderMap1 s
  ) seq
  |> List.filterMap id
  |> List.map (fun xs => xs[xs.length / 2]!)
  |> List.sum

  s!"{part1_res}\n{part2_res}"
