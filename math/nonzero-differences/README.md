# New terms for three OEIS "more terms needed" sequences

Sequences about integer sequences whose **differences of all degrees are nonzero**
(Gus Wiseman, 2019). All three were tagged `more` and had not been extended since 2019.
Checked against the OEIS database snapshot of 2026-09-27 (`github.com/oeis/oeisdata`):
none of the new values appear in any entry or b-file.

## A325850 — permutations of [n] whose differences of all degrees are nonzero

Known: a(0)..a(10). New:

| n | a(n) | verification |
|---|---|---|
| 11 | 18907320 | fast DFS, second DFS, literal brute force |
| 12 | 222828774 | fast DFS, second DFS, literal brute force |
| 13 | 2820233084 | fast DFS, second (independent) DFS |
| 14 | 38928266496 | fast DFS |
| 15 | (running) | |

## A325851 — compositions of n whose differences of all degrees are nonzero

Known: a(0)..a(22). New: a(23)..a(40), see `b325851.txt`
(a(23..28) also confirmed by literal brute force over all 2^(n-1) compositions).

## A325875 — compositions of n whose differences of all degrees > 1 are nonzero

Known: a(0)..a(20). New: a(21)..a(40), see `b325875.txt`
(a(21..28) also confirmed by literal brute force).

## Method

Append elements one at a time. If the right-hand diagonal of the difference triangle is
`d[0..L-1]`, appending `x` gives the new diagonal `x - P_i` with `P_i = d[0]+...+d[i-1]`
(`P_0 = 0`). So `x` is admissible iff it avoids every prefix sum `P_i` (for degrees `i >= D`),
which is one bitmask per search node. For permutations the complement symmetry
`x -> n+1-x` halves the work.

- `a325850.c` — permutations (OpenMP): `gcc -O3 -fopenmp a325850.c -o a && ./a 14`
- `compositions.c` — compositions: `./comp D lo hi` (D=1: A325851, D=2: A325875)
- `brute.c` — independent literal check (builds the full difference table of every sequence)
