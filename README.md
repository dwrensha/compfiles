# math-puzzles-in-lean4

Math puzzles and their solutions, formalized in [Lean 4](https://github.com/leanprover/lean4).

This is a continuation of
the work in the Lean 3 repo https://github.com/dwrensha/math-puzzles-in-lean.

## dashboard

A list of all the problems and their status is
available as a [dashboard](https://dwrensha.github.io/math-puzzles-in-lean4/)
that gets automatically updated on every push to the `main` branch of this repo.

## building

Make sure you have [`elan`](https://github.com/leanprover/elan) installed.
Then do:

```
$ lake exe cache get
$ lake build
```

## extracting problems

This repo defines some [/MathPuzzles/Meta/ProblemExtraction.lean](special command wrappers)
to support problem extraction.

To generate problem statements with all solution information stripped, do:
```
$ lake exe extractProblems
```
and then look in the `_extracted/` directory.

## contributing

Contributions are welcome!
You may take credit for you work by adding yourself
to the "authors" field in the copyright header.

## videos

|  |  |
| ----- | ---- |
| [IMO 1964 Problem 4](/MathPuzzles/Imo1964Q4.lean) | [<img src="http://img.youtube.com/vi/TOzS4aC_K1g/maxresdefault.jpg" height="120px">](http://youtu.be/TOzS4aC_K1g)|
| [IMO 1964 Problem 1b](/MathPuzzles/Imo1964Q1B.lean) | [<img src="http://img.youtube.com/vi/9d2nicgd68Q/maxresdefault.jpg" height="120px">](http://youtu.be/9d2nicgd68Q)|
