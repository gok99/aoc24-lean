import Batteries
import Aoc
import Aoc.Lib.List

open Std

def cart {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  xs.flatMap (λ x => ys.map (λ y => (x, y)))

def diff (x: Int) (y: Int) : Int := (Int.natAbs (Int.sub ↑x ↑y))

def unique (cond: List α → α → Bool) (xs : List α) : List α :=
  xs.foldr (λ x acc => if cond acc x then acc else x :: acc) []

def print_grid (grid : Array (Array Char)) : String :=
  grid.foldl (λ acc row => acc ++
    (row.foldl (λ acc c => acc.push c) "" ++ "\n")) ""

def all_pairs : List α → List (α × α)
  | [] => []
  | x :: xs => xs.map (λ y => (x, y)) ++ all_pairs xs

def inbetween_diffs (x_diff: Int) (y_diff: Int) :=
  if x_diff % 3 == 0 && y_diff % 3 == 0 then
    some (x_diff / 3, y_diff / 3)
  else
    none

def antinode_candidates (p: (Int × Int) × (Int × Int)) : List (Int × Int) :=
  let ((x1, y1), (x2, y2)) := p
  let (p1_left, p1_below) := (if y1 <= y2 then true else false, if x1 >= x2 then true else false)
  let (x_diff, y_diff) := (diff x1 x2, diff y1 y2)
  let inbet := inbetween_diffs x_diff y_diff

  match (p1_left, p1_below) with
  -- up right
  | (true, true) => [(x1 + x_diff, y1 - y_diff), (x2 - x_diff, y2 + y_diff)]
    ++ (inbet.map (λ (x, y) => [(x1 - x, y1 + y), (x2 + x, y2 - y)]) |>.getD [])
  -- down right
  | (true, false) => [(x1 - x_diff, y1 - y_diff), (x2 + x_diff, y2 + y_diff)]
    ++ (inbet.map (λ (x, y) => [(x1 + x, y1 + y), (x2 - x, y2 - y)]) |>.getD [])
  -- up left
  | (false, true) => [(x1 + x_diff, y1 + y_diff), (x2 - x_diff, y2 - y_diff)]
    ++ (inbet.map (λ (x, y) => [(x1 - x, y1 - y), (x2 + x, y2 + y)]) |>.getD [])
  -- down left
  | (false, false) => [(x1 - x_diff, y1 + y_diff), (x2 + x_diff, y2 - y_diff)]
    ++ (inbet.map (λ (x, y) => [(x1 + x, y1 - y), (x2 - x, y2 + y)]) |>.getD [])

def antinode_constraints2 (p: (Int × Int) × (Int × Int)) :  (Int × Int → Bool) :=
  let ((x1, y1), (x2, y2)) := p
  let (x_diff, y_diff) := (diff x1 x2, diff y1 y2)
  let gcd := Int.gcd x_diff y_diff
  let (x_diff, y_diff) := (x_diff / gcd, y_diff / gcd)
  let grad_sign := if (x1 - x2) * (y1 - y2) < 0 then -1 else 1

  -- (x_diff, y_diff, x1, y1)
  fun (tx, ty) => (tx - x1) % x_diff == 0 &&
    ((tx - x1) / x_diff) * y_diff * grad_sign == (ty - y1)

def is_in_grid (width: Nat) (height: Nat) (p: Int × Int) :=
  let (x, y) := p
  x >= 0 && x < height && y >= 0 && y < width

def count_hash (grid: Array (Array Char))  :=
  grid.foldl (λ acc row =>
    acc + row.foldl (λ acc c => if c == '#' then acc + 1 else acc) 0) 0

def main : IO Unit := IO.interact $ λ input ↦
  let reports := lines input
    |> List.toArray ∘ List.map (List.toArray ∘ String.toList)
  let width := reports[0]!.size
  let height := reports.size
  let in_grid := is_in_grid width height
  let all_coords := cart (List.range height) (List.range width)

  let init : HashMap Char (List (Int × Int)) := all_coords
    |> List.foldl (λ map (x, y) =>
      let c := reports[x]![y]!
      if c == '.' then map else
      map.alter c (fun o => (↑x, ↑y) :: (o.getD []))) HashMap.empty

  let part1 := init.values |>.map all_pairs
    |>.flatMap fun l => l.map antinode_candidates
    |>.flatten |>.filter in_grid

  let part2 := init.values |>.map all_pairs
    |>.flatMap (λ l => l.map antinode_constraints2)
    |> λ p2 => all_coords.filter (λ (x,y) => p2.any (λ f => f (x,y)))

  let new_reports := part2.foldl (λ reports (x1, x2) =>
    reports.modify x1 (λ row => row.modify x2 (λ _ => '#'))
  ) reports


  s! "{count_hash new_reports}"
