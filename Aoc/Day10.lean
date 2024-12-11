import Batteries
import Aoc
import Aoc.Lib.List

open Std

abbrev Grid := Array (Array Nat)
abbrev Pos := Int × Int
abbrev dirs: List Pos := [(0, 1), (0, -1), (1, 0), (-1, 0)]

def get_zeroes (grid: Grid) : List Pos :=
  (grid.foldl (λ (coord, acc) row =>
    row.foldl (λ (coord, acc) cell =>
      if cell == 0 then
        ((coord.1, coord.2 + 1), coord :: acc)
      else
        ((coord.1, coord.2 + 1), acc)
    ) ((coord.1 + 1, 0), acc)
  ) ((-1,0), [])).snd

def in_bound (pos: Pos) (grid: Grid) : Bool :=
  pos.1 >= 0 && pos.1 < grid.size &&
  pos.2 >= 0 && (pos.2 < grid[0]!.size)

def is_valid_pos (pos1: Pos) (pos2: Pos) (grid: Grid) : Bool :=
  let (x1, y1) := pos1
  let (x2, y2) := pos2
  grid[x1.toNat]![y1.toNat]! + 1 == grid[x2.toNat]![y2.toNat]!

partial def acc_paths (grid: Grid) (pos: Pos) (seen: HashSet Pos) : List (List Pos) :=
  let (x, y) := pos
  let seen := seen.insert pos

  if grid[x.toNat]![y.toNat]! == 9
  then
    [[pos]]
  else

  let paths: List (List Pos) := dirs.foldl (λ acc dir  =>
    let (dx, dy) := dir
    let new_pos := (x + dx, y + dy)
    if in_bound new_pos grid &&
      is_valid_pos pos new_pos grid &&
      !seen.contains new_pos
    then
      let paths := acc_paths grid new_pos seen
      paths.map (λ path => pos :: path) ++ acc
    else
      acc
  ) []
  paths

def unique (l: List (Int × Int)) : List (Int × Int) :=
  l.foldl (λ acc x =>
    if acc.contains x then
      acc
    else
      x :: acc
  ) []

def main : IO Unit := IO.interact $ λ input ↦
  let input:= lines input
    |>.map (List.map (String.toNat! ∘ Char.toString) ∘ String.toList)
    |>.toArray |> (Array.map List.toArray)

  let zeroes: List (Int × Int) := get_zeroes input
  let res := zeroes |>.map (fun s => acc_paths input s HashSet.empty)

  let part1 := res
    |>.map (fun l =>
      (l.map (fun p => p.reverse.head?.getD (-1, -1))
      |> unique |>.length))
    |>.sum

  let part2 := res |>.map List.length |>.sum

  s! "{part1}\n{part2}"
