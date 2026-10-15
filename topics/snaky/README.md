# Snaky within 19 Maker moves

**An independently checked certificate forces Snaky within 19 Maker moves.**
This improves the public bound located by the 15 October 2026 audit, from 20.
See `RESULT.md` for claims and limits,
`STATE.md` for the current frontier, and `NOVELTY.md` for the pre-search audit.

From the repository root, verify the final certificate and rejection controls:

```sh
python3 topics/snaky/reproduce.py
```

This command uses only Python's standard library and runs serially. Add
`--reconstruct` to repeat the bounded construction from the pinned source data
and require an identical certificate; add `--baselines` for the baseline audits.
Constructor and verifier share the declarative file interface, not checking code.

`SPECIFICATION.md` defines the game and certificate rules. `SOUNDNESS.md` explains
why accepted rules yield a policy against all infinite-board replies. Public
data and attribution live in `reference/`; construction tools in `constructor/`;
independent checking in `verification/`; formal proof sources in `formal/`.

All work is local on a unique research branch. Do not merge another topic,
publish, or push results without the user's publication authorization.
