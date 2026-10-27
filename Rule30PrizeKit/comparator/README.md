# Comparator challenges

Before a maintainer marks a full solution **Human Verified**, they run Lean's
[comparator](https://github.com/leanprover/comparator), the highest standard for checking a proof that
may be adversarial. The automated verifier's replay (`../Check.lean`) loads the compiled submission
directly. Comparator instead exports the proof from the sandbox and checks it outside.

Comparator needs Linux with [landrun](https://github.com/Zouuup/landrun) and a `lean4export` built
for Lean 4.35.0. Use a fresh checkout in which no submission has been built.

```sh
cp /path/to/submission/Rule30Submission.lean .   # into the kit
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty -E PATH="$PATH" \
  --working-directory "$(pwd)" -- \
  bash -c 'lake env /path/to/comparator comparator/problem1.json'
```

- `Rule30Challenge.lean` states the four official targets with `sorry`.
- `problem1.json`, `not_problem1.json`, `problem2.json` and `not_problem2.json` are the matching configs.

Status: these configs have not been run yet. Comparator and landrun do not run on macOS, where this kit
was built.
