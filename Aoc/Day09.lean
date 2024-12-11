import Batteries
import Aoc
import Aoc.Lib.List

open Std

def pp_repeat (s: String) (n: Nat) : String :=
  (List.range n).foldl (λ acc _ => acc ++ s) ""

def pp_disk (disk: List (Nat × Nat)) (free: List (Nat × Nat)) :=
  match disk, free with
  | (id, l1) :: xs, (_, l2) :: ys =>
    (pp_repeat (toString id) l1)  ++ (pp_repeat "." l2)  ++ pp_disk xs ys
  | (id, l1) :: xs, [] =>
    (pp_repeat (toString id) l1) ++ pp_disk xs []
  | _, _ => ""

def flatten_disk (disk: List (Nat × Nat)) :=
  disk.foldr (λ (id, l) acc => (List.range l).map (λ _ => id) ++ acc) []

def parse_disk (c: Nat) (xs: List Nat) : (List (Nat × Nat) × List (Nat × Nat)) :=
  match xs with
  | a :: b :: xs => match parse_disk (c + 1) xs with
    | (disk, free) => ((c, a) :: disk, (c, b) :: free)
  | a :: [] => ([(c, a)], [])
  | [] => ([], [])

def combine (disk: List (Nat × Nat)) filled :=
  match disk, filled with
  | a :: xs, as :: ys =>
    (a :: as) ++ (combine xs ys)
  | a :: xs, [] => a :: xs
  | [], [] => []
  | _, _ => panic! "combine: disk and acc have incompatible lengths!"

partial def h disk_rev free_alloc acc :=
    match disk_rev, free_alloc with
    | (id1, l1) :: xs, ((id2, l2), frees) :: ys =>
      if id1 > id2 then
        if l1 > l2 then
          h ((id1, l1 - l2) :: xs) ys (((id1, l2) :: frees).reverse :: acc)
        else if l1 < l2 then
          h xs (((id2, l2 - l1), (id1, l1) :: frees) :: ys) acc
        else
          h xs ys (((id1, l1) :: frees).reverse :: acc)
      else -- combine and produce new disk, frees
        combine disk_rev.reverse (frees :: acc).reverse
    | _ :: _, [] => combine disk_rev.reverse acc.reverse
    | _, _ => panic! "defrag: disk and free_alloc have incompatible lengths!"

def defrag (disk: List (Nat × Nat)) (free: List (Nat × Nat)) : List (Nat × Nat) :=
  let new_disk := disk.reverse
  let free_alloc : List ((Nat × Nat) × List (Nat × Nat)) :=
    free.map (λ p => (p, []))
  h new_disk free_alloc []

-- fit as many whole blocks in free as possible, returning the remaining free and remaining blocks
def check (free: Nat × Nat) (blocks: List (Nat × Nat)) : (Nat × Nat × (List (Nat × Nat))) × List (Nat × Nat) :=
  let (f_id, f_len) := free
  match blocks with
  | [] => ((f_id, f_len, []), [])
  | (b_id, b_len) :: bs =>
    if f_len >= b_len && b_id > f_id then
      let ((f_id, f_len', l), blocks) := check (f_id, f_len - b_len) bs
      ((f_id, f_len', (b_id, b_len) :: l), blocks)
    else
      let (free, blocks) := check free bs
      (free, (b_id, b_len) :: blocks)

inductive Segments
| Block : Nat -> Nat -> Segments
| Free : Nat -> Segments

def get_segments (disk: List (Nat × Nat)) (free: List (Nat × Nat)) : List Segments :=
  match disk, free with
  | (id, l1) :: xs, (_, l2) :: ys =>
    Segments.Block id l1 :: Segments.Free l2 :: get_segments xs ys
  | (id, l1) :: xs, [] =>
    Segments.Block id l1 :: get_segments xs []
  | _, _ => []

def merge_frees (blocks: List Segments) (acc_free := 0) : List Segments :=
  match blocks with
  | Segments.Free l :: xs => merge_frees xs (l + acc_free)
  | Segments.Block id l :: xs => (if acc_free > 0 then [Segments.Free acc_free] else [])
    ++ Segments.Block id l :: merge_frees xs acc_free
  | [] => if acc_free > 0 then [Segments.Free acc_free] else []

def try_match (block: Segments) (blocks: List Segments) : Bool × Segments × List Segments :=
  match block, blocks with
  | Segments.Block id l, Segments.Free n :: xs =>
    if n >= l then
      let diff := n - l
      let t := if diff > 0 then [Segments.Free diff] else []
      (true, Segments.Block id l, (Segments.Block id l :: t) ++ xs)
    else
      let (b, block, blocks) := try_match (Segments.Block id l) xs
      (b, block, Segments.Free n :: blocks)
  | Segments.Block id l, Segments.Block id2 l2 :: xs =>
    let (b, block, blocks) := try_match (Segments.Block id l) xs
    (b, block, Segments.Block id2 l2 :: blocks)
  | Segments.Block _ _, [] => (false, block, [])
  | Segments.Free _, _ => (false, block, [])

partial def defrag2 (disk: List Segments) : List Segments :=
  match disk with
  | Segments.Block id l :: xs =>
    let (b, block, blocks) := try_match (Segments.Block id l) xs.reverse
    if b
    then (Segments.Free l) ::  defrag2 blocks.reverse
    else block :: defrag2 blocks.reverse
  | Segments.Free l :: xs => Segments.Free l :: defrag2 xs
  | [] => []

def pp_segment_list (blocks: List Segments) :=
  blocks.foldl (λ acc x =>
    match x with
    | Segments.Block id l => acc ++ pp_repeat (toString id) l
    | Segments.Free l => acc ++ pp_repeat "." l) ""

def flatten_segment_list (blocks: List Segments) : List Nat :=
  blocks.foldl (λ acc x =>
    match x with
    | Segments.Block id l => (List.range l).map (λ _ => id) ++ acc
    | Segments.Free l => (List.range l).map (λ _ => 0) ++ acc) []

def main : IO Unit := IO.interact $ λ input ↦
  let (disk, free) := lines input
    |>.flatMap String.toList |>.map (String.toNat! ∘ Char.toString)
    |> parse_disk 0

  let part1 := defrag disk free |> flatten_disk |>.foldlIdx (λ i acc x => acc + i * x) 0

  let part2 := get_segments disk free |>.reverse |> defrag2 |> flatten_segment_list
    |>.foldlIdx (λ i acc x => acc + i * x) 0

  s! "{part1}\n{part2}"
