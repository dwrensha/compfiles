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

This repo defines some [special commands](/Compfiles/Meta/ProblemExtraction.lean)
to support problem extraction.

* A `problem_file` command marks a file that should participate in problem extraction.
* A `problem` declaration is the main theorem to be proved.
* A `determine` declaration indicates data the must be provided as part of the solution.
* A `snip begin` ... `snip end` sequence indicates commands that should be omitted
  in the extracted problem.

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
| [IMO 1964 Problem 4](/Compfiles/Imo1964P4.lean) | [<img src="http://img.youtube.com/vi/TOzS4aC_K1g/maxresdefault.jpg" height="120px">](http://youtu.be/TOzS4aC_K1g)|
| [IMO 1964 Problem 1b](/Compfiles/Imo1964P1.lean) | [<img src="http://img.youtube.com/vi/9d2nicgd68Q/maxresdefault.jpg" height="120px">](http://youtu.be/9d2nicgd68Q)|
