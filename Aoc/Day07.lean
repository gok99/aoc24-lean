import Batteries
import Aoc
import Aoc.Lib.List

open Std

inductive Elem
| Num : Nat -> Elem
| Op : String -> Elem

def interleave (xs : List Nat) (ops : List String) : List (List Elem) :=
  match xs with
  | [] => []
  | [a] => [[Elem.Num a]]
  | x::xs => interleave xs ops
    |>.flatMap (λ ys => ops.map (λ op => Elem.Num x :: Elem.Op op :: ys))

def concatNumbers (a : Nat) (b : Nat) : Nat :=
  a * (Nat.pow 10 (Nat.toDigits 10 b).length) + b

def eval (xs : List Elem) : Nat :=
  let rec aux (acc : Nat) (xs : List Elem) : Nat :=
    match xs with
    | [] => acc
    | Elem.Num x::xs => aux x xs
    | Elem.Op "+"::Elem.Num x::xs => aux (acc + x) xs
    | Elem.Op "*"::Elem.Num x::xs => aux (acc * x) xs
    | Elem.Op "||"::Elem.Num x::xs => aux (concatNumbers acc x) xs
    | _ => panic! "invalid expression"
  aux 0 xs

def res (a: List (String × List Nat)) (ops: List String) : Nat :=
  a.map (λ (x, y) => (x.toNat!, interleave y ops |>.map eval |>.contains x.toNat!))
    |> List.foldl (λ acc x => if x.snd then acc + x.fst else acc) 0

def main : IO Unit := IO.interact $ λ input ↦
  let a := lines input
    |> List.map ((λ (x, y) => (x, List.map String.toNat! (words y))) ∘ List.first2 ∘ (String.splitOn (sep := ":")))
  s!"{res a ["+", "*"]}\n{res a ["+", "*", "||"]}"
