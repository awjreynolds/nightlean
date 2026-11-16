# Issue tracker: GitHub

The canonical issue tracker is GitHub Issues in `awjreynolds/nightlean`.

The public map is [issue #1](https://github.com/awjreynolds/nightlean/issues/1). Link every decision, research task, and implementation task as a native child issue. Link blockers with GitHub issue dependencies so a new implementation agent sees the actual execution order.

## Wayfinding operations

- The map is a GitHub issue labelled `wayfinder:map`.
- Each ticket is a child issue of the map and has one `wayfinder:<type>` label: `research`, `prototype`, `grilling`, or `task`.
- Use GitHub's native sub-issue and issue dependency relationships. Keep the map's Decisions so far section updated when a ticket closes.
- Use `gh` inside the repository for issue, label, and relationship operations.

## Pull requests

Pull requests are not a request surface for triage.
