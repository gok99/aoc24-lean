import Aoc
import Aoc.Lib.List

def h (xs : List Int) : List Int :=
  match xs with
  | x :: y :: xs => (y - x) :: h (y :: xs)
  | _ => []

def strict_up (xs : List Int) :=
  List.map (fun x => x > 0 && x < 4) xs
def strict_down (xs : List Int) :=
  List.map (fun x => x < 0 && x > -4) xs

def check (xs : List Int) :=
  (strict_up xs).all id || (strict_down xs).all id

def part1 (xs : List Int) : Bool :=
  let diffs := h xs
  check diffs

def part2 (xs : List Int) : Bool :=
  let diffs := h xs
  let check_helper := λ xs f ↦
    f xs |> List.findIdx not

  if check diffs then true else
  let up_idx := check_helper diffs strict_up
  let down_idx := check_helper diffs strict_down

  ([ up_idx, up_idx + 1, down_idx, down_idx + 1 ].map
    (λ i ↦ (xs[i]?.map (fun _ =>
        check $ h (List.eraseIdx xs i))).getD false)
  ).any id

def main : IO Unit := IO.interact $ λ input =>
  let reports := lines input
    |> List.map (List.map String.toInt! ∘ words)

  let part1_res := reports.count2 part1
  let part2_res := reports.count2 part2

  s!"{part1_res}\n{part2_res}"
