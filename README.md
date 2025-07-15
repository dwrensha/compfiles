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

In this repo,
each solution (proof) is recorded inline, in the same file that its problem is declared.
In some situations, however, solution data is undesired.
For example, we might want a [website](https://dwrensha.github.io/compfiles/)
to display only the problem statement,
or we might
want to invoke an [IMO Grand Challenge](https://imo-grand-challenge.github.io/)
solver without providing spoilers.

To that end, this repo defines some [special commands](/ProblemExtraction.lean)
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

## extracting solutions

Sometimes it's useful to have a version of a solution
that does not depend on the `ProblemExtraction` library
(but still contains all proof information).
For example, you might want to share a fully worked solution
on https://live.lean-lang.org/.

To that end, the `extractProblems` tool described above
additionally extracts dependency-stripped solution files into the
`_extracted/solutions` directory.

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

The intention is that this solution checker could be used as a
grader for the [IMO Grand Challenge](https://imo-grand-challenge.github.io/).

## contributing

Contributions are welcome!
You may take credit for you work by adding yourself
to the "authors" field in the copyright header.

## external sources

Some problems were imported from external sources:

* [mathlib4/Archive/Imo](https://github.com/leanprover-community/mathlib4/tree/master/Archive/Imo).
* Gian Sanjaya's [Lean 3](https://github.com/mortarsanjaya/imo-A-and-N) and
  [Lean 4](https://github.com/mortarsanjaya/IMOSLLean4) formalizations of
  IMO shortlist problems.
* Joseph Myers's [IMOLean](https://github.com/jsm28/IMOLean/tree/main) repository.
* Roozbeh Yousefzadeh's [Imo-Steps](https://github.com/roozbeh-yz/IMO-Steps) repository.

## videos

|  |  |
| ----- | ---- |
| [IMO 1996 Problem 3](/Compfiles/Imo1996P3.lean) | [<img src="http://img.youtube.com/vi/5NbYtDfXfR4/maxresdefault.jpg" height="120px">](https://youtu.be/5NbYtDfXfR4)|
| [IMO 1987 Problem 4](/Compfiles/Imo1987P4.lean) | [<img src="http://img.youtube.com/vi/gi8ZTjRO-xI/maxresdefault.jpg" height="120px">](https://youtu.be/gi8ZTjRO-xI)|
| [IMO 1964 Problem 4](/Compfiles/Imo1964P4.lean) | [<img src="http://img.youtube.com/vi/TOzS4aC_K1g/maxresdefault.jpg" height="120px">](http://youtu.be/TOzS4aC_K1g)|
| [IMO 1964 Problem 1b](/Compfiles/Imo1964P1.lean) | [<img src="http://img.youtube.com/vi/9d2nicgd68Q/maxresdefault.jpg" height="120px">](http://youtu.be/9d2nicgd68Q)|
