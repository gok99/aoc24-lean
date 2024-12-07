import Aoc
import Aoc.Lib.List
import Batteries

-- absolutely attrocious
-- TODO: port part2 brute force

open Std

def Pos := Int × Int deriving BEq

inductive Expect
| Expect : Pos × Pos -> Expect
| Book : List (Nat × Nat) -> Expect

inductive Dir
| N : Dir
| E : Dir
| S : Dir
| W : Dir

inductive State
| C : Pos × Dir -> Array (Array Char) -> State

inductive State2
| C : Pos × Dir -> Array (Array Char) -> List Expect -> State2

def cart {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  xs.flatMap (λ x => ys.map (λ y => (x, y)))

def find_start (grid: Array (Array Char)) : Pos × Dir :=
  let cells := cart (List.range grid.size) (List.range grid[0]!.size)
  let m1 := (cells.find? (λ (x, y) => grid[x]![y]! == '^')).map (λ p => (p, Dir.N))
  let m2 := (cells.find? (λ (x, y) => grid[x]![y]! == 'v')).map (λ p => (p, Dir.S))
  let m3 := (cells.find? (λ (x, y) => grid[x]![y]! == '<')).map (λ p => (p, Dir.W))
  let m4 := (cells.find? (λ (x, y) => grid[x]![y]! == '>')).map (λ p => (p, Dir.E))

  let ((x,y), d) := (((m1.or m2).or m3).or m4).getD (dflt :=  ((0, 0), Dir.N))
  ((x,y), d)

def ended (state: State) : Bool :=
  match state with
  | State.C ((x, y), _) grid =>
    let width := grid[0]!.size
    let height := grid.size
    x < 0 || y < 0 || x >= height || y >= width

def new_pos (pos: Pos) (dir: Dir) : Pos :=
  let (x, y) := pos
  match dir with
  | Dir.N => (x - 1, y)
  | Dir.E => (x, y + 1)
  | Dir.S => (x + 1, y)
  | Dir.W => (x, y - 1)

def new_dir (dir: Dir) : Dir :=
  match dir with
  | Dir.N => Dir.E
  | Dir.E => Dir.S
  | Dir.S => Dir.W
  | Dir.W => Dir.N

def get_dir (x1: Int) (y1: Int) (x2: Int) (y2: Int) :=
  if x1 > x2 then Dir.N else
  if x1 < x2 then Dir.S else
  if y1 < y2 then Dir.E else
  if y1 > y2 then Dir.W else Dir.N

def step (state: State) : State :=
  match state with
  | State.C ((x, y), dir) grid =>
    let newGrid := grid.modify x.toNat (λ row => row.modify y.toNat (λ _ => 'X'))

    let (x_c, y_c) := new_pos (x, y) dir
    let candidate_no_good := x_c >= 0 && y_c >= 0 && x_c < grid.size && y_c < grid[0]!.size
      && grid[x_c.toNat]![y_c.toNat]! == '#'

    if candidate_no_good
    then
      let dir' := new_dir dir
      let (x', y') := new_pos (x, y) dir'
      State.C ((x', y'), dir') newGrid
    else
      State.C ((x_c, y_c), dir) newGrid

-- call every step
def loop_cond (book: List Expect) (pos: Pos) (isTurn: Bool) (grid: Array (Array Char)) : Bool × List Expect :=
  match book with
  | [] => (false , [])
  | (Expect.Book _) :: _ => (false, book)
  | (Expect.Expect ((x1 , y1), (x2, y2))) :: t =>
    if pos == (x1, y1) -- reached expected position
      then (grid[x2.toNat]![y2.toNat]! != '#', t) -- TODO: more conds
    else if (isTurn) -- path blocked
      then (false, t) -- never reaching (drop expected)
      else (false, book) -- might reach (keep expected)

-- call when you hit a wall
def process_book (book: List Expect) (turn_pos: Pos) (grid: Array (Array Char)) : List Expect :=
  let (x, y) := turn_pos
  let book' := (book.map (λ e => match e with
  | Expect.Expect _ => e
  | Expect.Book l => Expect.Book ((x.toNat, y.toNat) :: l))) ++ [Expect.Book [(x.toNat, y.toNat)]]
  match book' with
  | (Expect.Book l) :: t =>
    if l.length >= 3
    then match l.first3! with
    | ((x3, y3), (x2, y2), (x1, y1)) =>
      let ((x, y), (px, py)) := match get_dir x1 y1 x2 y2 with
      | Dir.N => ((x1, y1 + (y3 - y2)), (x1 + 1, y1 + (y3 - y2)))
      | Dir.E => ((x1 + (x3 - x2), y1), (x1 + (x3 - x2), y1 - 1))
      | Dir.S => ((x1, y1 - (y2 - y3)), (x1 - 1, y1 - (y2 - y3)))
      | Dir.W => ((x1 - (x2 - x3), y1), (x1 - (x2 - x3), y1 + 1))
      if ended (State.C ((px, py), Dir.N) grid) -- pos is outside grid
      then t --drop
      else Expect.Expect ((x,y), (px,py)) :: t
    else book'
  | _ => book'

def step2 (state: State2) (count: List (Int × Int)) : State2 × List (Int × Int) :=
  match state with
  | State2.C ((x, y), dir) grid book  =>
    let newGrid := grid.modify x.toNat (λ row => row.modify y.toNat (λ _ => 'X'))

    let (x_c, y_c) := new_pos (x, y) dir
    let candidate_no_good := x_c >= 0 && y_c >= 0 && x_c < grid.size && y_c < grid[0]!.size
      && grid[x_c.toNat]![y_c.toNat]! == '#'

    let (cond, book') := loop_cond book (x, y) candidate_no_good newGrid
    let count' := if cond then (x,y) :: count else count

    if candidate_no_good
    then
      let dir' := new_dir dir
      let (x', y') := new_pos (x, y) dir'
      let newBook := process_book book' (x, y) grid
      (State2.C ((x', y'), dir') newGrid newBook, count')
    else
      (State2.C ((x_c, y_c), dir) newGrid book', count')

def countCrosses (grid: Array (Array Char)) : List Pos :=
  let cells := cart (List.range grid.size) (List.range grid[0]!.size)
  cells.filter (λ (x, y) => grid[x]![y]! == 'X') |> List.map (λ (x, y) => (x, y))

def stepUntilEnd (fuel: Nat) (state: State) : State :=
  match fuel with
  | 0 => state
  | fuel + 1 => if ended state then state
    else stepUntilEnd fuel (step state)

def printGrid (grid: Array (Array Char)) : String :=
  grid.foldl (λ acc row =>
    acc ++ row.foldl (λ acc cell =>
      acc ++ cell.toString
    ) "" ++ "\n"
  ) ""

def printBook (book: List Expect) : String :=
  book.foldl (λ acc e =>
    acc ++ match e with
    | Expect.Expect ((x1, y1), (x2, y2)) => s!"({x1}, {y1}) -> ({x2}, {y2}) || "
    | Expect.Book l => (l.foldl (λ acc (x, y) => acc ++ s!"({x}, {y}) ") "") ++ "|| "
  ) "" ++ "\n"

def stepUntilEnd2 (fuel: Nat) (state: State2) (count: List (Int × Int)) (acc: String) : String × List (Int × Int) :=
  let defa: List (Int × Int) := count
  match fuel with
  | 0 => match state with
    | State2.C _ grid _ => (acc ++ printGrid grid, defa)
  | fuel + 1 => match state with
    | State2.C thing grid book =>
      if ended (State.C thing grid) then (acc ++ printGrid grid, defa)
      else
        let (state', count') := step2 state count
        stepUntilEnd2 fuel state' count' (acc ++ printBook book)

def main : IO Unit := IO.interact $ λ input =>
  let reports := lines input
    |> List.toArray ∘ List.map (List.toArray ∘ String.toList)
  let dim := (reports.size * reports[0]!.size)

  let init := State.C (find_start reports) (reports
    |> Array.map (Array.map (λ c => if c == '^'  then '.' else c)))

  let init2 := State2.C (find_start reports) (reports
    |> Array.map (Array.map (λ c => if c == '^'  then '.' else c))) []

  let part1_res := match stepUntilEnd dim init with
    | State.C _ grid => countCrosses grid

  let part2_res := stepUntilEnd2 dim init2 [] "" -- |> Prod.snd |> List.length

  s!"{part1_res.length}\n{part2_res}"
