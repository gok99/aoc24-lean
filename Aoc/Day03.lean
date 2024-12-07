import Aoc
import Aoc.Lib.List

-- I am a massochist

inductive Mode
  | Mul1 : Mode
  | Mul2 : Mode
  | Mul3 : Mode
  | MulNum1 : Mode
  | MulNum2 : Mode
  | Garbage : Mode

inductive InitPass
  | Do1 : Bool -> InitPass -- d
  | Do2 : Bool -> InitPass -- do
  | Do3 : Bool -> InitPass -- do(
  | Dont3 : Bool -> InitPass -- don
  | Dont4 : Bool -> InitPass -- don'
  | Dont5 : Bool -> InitPass -- don't
  | Dont6 : Bool -> InitPass -- don't(
  | Garbage : Bool -> InitPass

def upd_head [Inhabited α] (f : α → α) : List α → List α
  | [] => f default :: []
  | x :: xs => f x :: xs

def init_pass (mode : InitPass) (xs : List Char) : List Char :=
  match mode, xs with
  | InitPass.Do1 b, 'o' :: rest => init_pass (InitPass.Do2 b) rest
  | InitPass.Do2 b, '(' :: rest => init_pass (InitPass.Do3 b) rest
  | InitPass.Do3 _, ')' :: rest => init_pass (InitPass.Garbage true) rest
  | InitPass.Do2 b, 'n' :: rest => init_pass (InitPass.Dont3 b) rest
  | InitPass.Dont3 b, '\'' :: rest => init_pass (InitPass.Dont4 b) rest
  | InitPass.Dont4 b, 't' :: rest => init_pass (InitPass.Dont5 b) rest
  | InitPass.Dont5 b, '(' :: rest => init_pass (InitPass.Dont6 b) rest
  | InitPass.Dont6 _, ')' :: rest => init_pass (InitPass.Garbage false) rest

  | InitPass.Do1 b, a :: rest | InitPass.Do2 b, a :: rest | InitPass.Do3 b, a :: rest
    | InitPass.Dont3 b, a :: rest | InitPass.Dont4 b, a :: rest | InitPass.Dont5 b, a :: rest
    | InitPass.Dont6 b, a :: rest =>
    if b then a :: init_pass mode rest
    else init_pass mode rest

  | InitPass.Garbage b, 'd' :: rest => init_pass (InitPass.Do1 b) rest
  | InitPass.Garbage b, a :: rest =>
    if b then a :: init_pass mode rest
    else init_pass mode rest
  | _, [] => []

def parse (mode : Mode) (xs : List Char) (ctx: List Int) : List Int :=
  match mode, xs with
  | Mode.Mul1, 'u' :: rest => parse Mode.Mul2 rest []
  | Mode.Mul2, 'l' :: rest => parse Mode.Mul3 rest []
  | Mode.Mul3, '(' :: rest => parse Mode.MulNum1 rest []

  | Mode.MulNum1, ',' :: rest => parse Mode.MulNum2 rest ctx
  | Mode.MulNum1, a :: rest =>
    if a.isDigit && ctx.length <= 1 then
      let ctx' := upd_head (fun x => x * 10 + a.toString.toInt!) ctx
      parse Mode.MulNum1 rest ctx'
    else match a with
    | 'm' => parse Mode.Mul1 rest []
    | _ => parse Mode.Garbage rest []

  | Mode.MulNum2, ')' :: rest =>
    match ctx with
    | [a, b] => a * b :: parse Mode.Garbage rest []
    | _ => parse Mode.Garbage rest []
  | Mode.MulNum2, a :: rest =>
    if a.isDigit then
      if ctx.length == 1 then
        parse Mode.MulNum2 rest (a.toString.toInt! :: ctx)
      else if ctx.length == 2 then
        let ctx' := upd_head (fun x => x * 10 + a.toString.toInt!) ctx
        parse Mode.MulNum2 rest ctx'
      else parse Mode.Garbage rest ctx
    else match a with
    | 'm' => parse Mode.Mul1 rest []
    | _ => parse Mode.Garbage rest []

  | _, 'm' :: rest => parse Mode.Mul1 rest []
  | _, _ :: rest => parse Mode.Garbage rest []

  | _ , [] => []

def part1 (xs : String) : List Int := parse Mode.Garbage xs.toList []

def part2 (xs : String) : List Int :=
  parse Mode.Garbage (init_pass (InitPass.Garbage true) xs.toList) []

def main : IO Unit := IO.interact $ λ input =>
  let reports := lines input

  let part1_res := (reports.map part1).flatten.sum
  let part2_res := (part2 (reports.foldl (fun acc x => acc ++ x) "")).sum

  s!"{part1_res}\n{part2_res}"
