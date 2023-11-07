# Compfiles: Catalog Of Math Problems Formalized In Lean, Emphasizing Solutions

A collection of olympiad-style math problems and their solutions,
formalized in [Lean 4](https://github.com/leanprover/lean4).

## dashboard

A list of all the problems and their status is
available as a [dashboard](https://dwrensha.github.io/compfiles/)
that gets automatically updated on every push to the `main` branch of this repo.

## building

Make sure you have [`elan`](https://github.com/leanprover/elan) installed.
Then do:

```
$ lake exe cache get
$ lake build
```

## extracting problems

This repo defines some [special commands](/ProblemExtraction.lean)
to support problem extraction.

* A `problem_file` command marks a file that should participate in problem extraction.
* A `problem` declaration is the main theorem to be proved.
  The body of the declaration (everything to the right of `:=`) is replaced by `sorry`
  in the extracted problem.
* A `determine` declaration indicates data the must be provided as part of the solution.
  Like with `problem`, the body of the declaration is replaced by `sorry` in the
  extracted problem.
* A `snip begin` ... `snip end` sequence indicates commands that should be omitted
  in the extracted problem.

To generate problem statements with all solution information stripped, do:
```
$ lake exe extractProblems
```
and then look in the `_extracted/problems` directory.

Files in the `_extracted/solutions` directory retain their solution
information, but are stripped of their dependency on
the `ProblemExtraction` library.

## checking solutions

The `checkSolution` executable takes as input a problem ID
and a path to a lean source code file. For example:
```
$ lake exe checkSolution Imo2022P2 _extracted/solutions/Imo2022P2.lean
```
This will check that the extracted solution file
`_extracted/solutions/Imo2022P2.lean`
does indeed pass verification for problem `Imo2022P2`. It will print the terms
for any `determine` declarations in the solution, so that
they can be judged by a human. In this example, that will look like:
```
determine Imo2022P2.solution_set := {fun x => 1 / x}
```

This solution checker could be used as a
grader for the for the [Imo Grand Challenge](https://imo-grand-challenge.github.io/).

## contributing

Contributions are welcome!
You may take credit for you work by adding yourself
to the "authors" field in the copyright header.

## videos

|  |  |
| ----- | ---- |
| [IMO 1964 Problem 4](/Compfiles/Imo1964P4.lean) | [<img src="http://img.youtube.com/vi/TOzS4aC_K1g/maxresdefault.jpg" height="120px">](http://youtu.be/TOzS4aC_K1g)|
| [IMO 1964 Problem 1b](/Compfiles/Imo1964P1.lean) | [<img src="http://img.youtube.com/vi/9d2nicgd68Q/maxresdefault.jpg" height="120px">](http://youtu.be/9d2nicgd68Q)|
