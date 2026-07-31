# FC100

FC100 is a Lean benchmark package built from the
[`formal-conjectures`](https://github.com/google-deepmind/formal-conjectures)
repository at commit
[`7a41db3`](https://github.com/google-deepmind/formal-conjectures/commit/7a41db3d761324599812d6ca6cb6a9f311046dc7).
It contains the two upstream `Set1` benchmarks:

- `FC100Open`: the 100 research-open declarations in `FC100OpenSet1`.
- `FC100Solved`: the 100 non-open declarations in `FC100SolvedSet1`.

[`selection.json`](selection.json) is the authoritative list of benchmark
declarations and source files. The targets occupy 88 open and 81 solved source
files, with their proofs represented by `sorry`. Because Lean imports whole
files, these files also retain supporting and non-target declarations; 12
source files are used by both sets.

[`FC100Open.lean`](FC100Open.lean) and
[`FC100Solved.lean`](FC100Solved.lean) are the aggregate imports. Build both
libraries with:

```sh
lake build
```
