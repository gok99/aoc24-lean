import Aoc
import Aoc.Lib.List

def NextF := Int × Int -> Int × Int

def north : NextF := λ (x,y) => (x - 1, y)
def south : NextF := λ (x,y) => (x + 1, y)
def east : NextF := λ (x,y) => (x, y + 1)
def west : NextF := λ (x,y) => (x, y - 1)
def north_east : NextF := λ (x,y) => (x - 1, y + 1)
def north_west : NextF := λ (x,y) => (x - 1, y - 1)
def south_east : NextF := λ (x,y) => (x + 1, y + 1)
def south_west : NextF := λ (x,y) => (x + 1, y - 1)

def cart {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  xs.flatMap (λ x => ys.map (λ y => (x, y)))

inductive State : Type
  | Default : State
  | X : State
  | M : State
  | A : State

def check_line (width: Int) (height: Int)  (grid: Array (Array Char)) (dir: Int × Int -> Int × Int)
  (fuel: Nat) (state: State) (start: Int × Int) (count : Nat) : Nat :=
  let (x, y) := start
  match fuel with
  | 0 => count
  | fuel' + 1 =>
    if x >= width || y >= height || x < 0 || y < 0 then count
    else
      let next_pos := dir start
      match state, grid[x.toNat]![y.toNat]! with
      | _, 'X' => check_line width height grid dir fuel' State.X next_pos count
      | State.X, 'M' => check_line width height grid dir fuel' State.M next_pos count
      | State.M, 'A' => check_line width height grid dir fuel' State.A next_pos count
      | State.A, 'S' => check_line width height grid dir fuel' State.Default next_pos (count + 1)
      | _, _ => check_line width height grid dir fuel' State.Default next_pos count

def default_coord := (-1, -1)

def check_line2 (width: Int) (height: Int)  (grid: Array (Array Char)) (dir: Int × Int -> Int × Int)
  (fuel: Nat) (state: State) (start: Int × Int) (mid: (Int × Int)) (count : List (Int × Int)) : List (Int × Int) :=
  let (x, y) := start
  match fuel with
  | 0 => count
  | fuel' + 1 =>
    if x >= width || y >= height || x < 0 || y < 0 then count
    else
      let next_pos := dir start
      match state, grid[x.toNat]![y.toNat]! with
      | _, 'M' => check_line2 width height grid dir fuel' State.M next_pos default count
      | State.M, 'A' => check_line2 width height grid dir fuel' State.A next_pos start count
      | State.A, 'S' => check_line2 width height grid dir fuel' State.Default next_pos default (mid :: count)
      | _, _ => check_line2 width height grid dir fuel' State.Default next_pos default count

def part1 (reports: Array (Array Char)) :=
  let width := reports[0]!.size
  let height := reports.size

  let top_row := List.range' 1 (width - 2) 1 |> List.map (λ x => (0, x))
  let bot_row := List.range' 1 (width - 2) 1 |> List.map (λ x => (height - 1, x))
  let left_col := List.range' 1 (height - 2) 1 |> List.map (λ y => (y, 0))
  let right_col := List.range' 1 (height - 2) 1 |> List.map (λ y => (y, width - 1))

  let starts :=
    cart top_row [south, south_east, south_west] ++
    cart bot_row [north, north_east, north_west] ++
    cart left_col [east, south_east, north_east] ++
    cart right_col [west, south_west, north_west] ++
    cart [(0, 0)] [south_east, south, east] ++
    cart [(0, width - 1)] [south_west, south, west] ++
    cart [(height - 1, 0)] [north_east, north, east] ++
    cart [(height - 1, width - 1)] [north_west, north, west]

  starts.map
    (λ ((x, y), dir) => check_line width height reports dir (Nat.max height width) State.Default (↑x, ↑y) 0)
    |> List.sum

def part2 (reports: Array (Array Char)) :=
  let width := reports[0]!.size
  let height := reports.size

  let top_row := List.range' 1 (width - 2) 1 |> List.map (λ x => (0, x))
  let bot_row := List.range' 1 (width - 2) 1 |> List.map (λ x => (height - 1, x))
  let left_col := List.range' 1 (height - 2) 1 |> List.map (λ y => (y, 0))
  let right_col := List.range' 1 (height - 2) 1 |> List.map (λ y => (y, width - 1))

  let f : (Nat × Nat) × NextF -> List (Int × Int) :=
    λ ((x, y), dir) => check_line2 width height reports dir (Nat.max height width) State.Default (x, y) default []

  let down_right := (cart (top_row ++ left_col ++ [(0, 0)]) [south_east]).map f |> List.flatten
  let up_right := (cart (bot_row ++ left_col ++ [(height - 1, 0)]) [north_east]).map f |> List.flatten

  let up_left := (cart (bot_row ++ right_col ++ [(height - 1, width - 1)]) [north_west]).map f |> List.flatten
  let down_left := (cart (top_row ++ right_col ++ [(0, width - 1)]) [south_west]).map f |> List.flatten

  let x1 := down_right.filter (λ x => up_right.contains x)
  let x2 := down_right.filter (λ x => down_left.contains x)
  let x3 := up_right.filter (λ x => up_left.contains x)
  let x4 := down_left.filter (λ x => up_left.contains x)

  -- intersection
  x1 ++ x2 ++ x3 ++ x4

def main : IO Unit := IO.interact $ λ input =>
  let reports := lines input
    |> List.toArray ∘ List.map (List.toArray ∘ String.toList)

  let part1_res := part1 reports
  let part2_res := part2 reports |>.length

  s!"{part1_res}\n{part2_res}"
