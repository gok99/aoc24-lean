import Aoc
import Aoc.Lib.List
import Aoc.Lib.Parsec
import Batteries

open Std.Internal.Parsec.String
open Std.Internal.Parsec

-- Thanks Kiran!

def charArrayToString (xs : Array Char) : String :=
  xs.foldl (fun acc x => acc ++ x.toString) ""

inductive Inst : Type
  | Res : Nat -> Inst
  | Do : Bool -> Inst

def getMul : Parser Inst := do
  skipString "mul("
  let n1 ← many1 digit
  skipString ","
  let n2 ← many1 digit
  skipString ")"
  pure $ Inst.Res ((charArrayToString n1).toNat! * (charArrayToString n2).toNat!)

def getOp : Parser Inst :=
   (skipString "do()" *> (pure $ Inst.Do true)) <|>
   (skipString "don't()" *> (pure $ Inst.Do false))

def mulOrOp : Parser Inst :=
  getMul <|> getOp

def part1 (s: String) : Nat := s
  |> (allMatches getMul).run
  |> Except.map (List.map (λ ins => match ins with | Inst.Res n => n | _ => 0))
  |> Except.map List.sum
  |> Except.toOption
  |> Option.getD (dflt := 0)

def part2 (s : String) : List Nat := s
  |> (allMatches mulOrOp).run
  |> Except.map (List.foldl
      (λ acc ins =>
        let (do', sum) := acc
        match ins with
        | Inst.Res n => if do' then (do', n :: sum) else (do', sum)
        | Inst.Do b => (b, sum))
      (true, []))
  |> Except.map Prod.snd
  |> Except.toOption
  |> Option.getD (dflt := [])

def main : IO Unit := IO.interact $ λ input =>
  let reports := lines input

  let part1_res := (reports.map part1).sum
  let part2_res := (part2 (reports.foldl (fun acc x => acc ++ x) "")).sum

  s!"{part1_res}\n{part2_res}"
