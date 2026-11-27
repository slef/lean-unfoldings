# Unfoldings in Lean: the book

An interactive guide to the *abstract* statements of the `Unfoldings` library:
`Unfoldings/Source/Abstract.lean` and `Unfoldings/Cap/Abstract.lean`. Every
definition and theorem statement of these files is shown as compiled, with
hoverable and hyperlinked identifiers and axiom badges. Explanations are
interleaved, and each theorem has a reading path: the definitions one must read
to check what it says.

The generator is adapted from the book of [lean-bst](https://github.com/slef/lean-bst).

## Build

```sh
lake build Unfoldings.Cap.Abstract Unfoldings.Source.Abstract   # in the repository root
cd book
npm ci
npm run extract        # Lean → build/lean-data.json
npm run build          # → dist/
npm test               # the geometry of the figures, and the citation code
npm run lint           # coherence of the sources (numbers, citations, coverage)
npm run check:pages    # every built page in headless Chrome or Chromium
npm run check          # build, lint, test and check:pages together
npm run verify:bib     # bibliography entries against Crossref, DataCite and arXiv
npm run serve          # http://localhost:8000
```

`npm run extract` reads the `.ilean` files of the two abstract modules and runs
`lean/Export.lean` through `lake env lean`. It needs only those modules and
their imports to be built, not the whole library. It fails if the compiled data
is stale with respect to the sources. `dist/` is a static site; nothing is
published automatically.

## Layout

| Path | Contents |
|---|---|
| `src/book.json` | Title, repository URL, KaTeX macros, and the order of the pages. Numbers are assigned by the build. |
| `src/bibliography.json` | Every work the book cites |
| `src/chapters/<part>/*.md` | One file per page |
| `src/assets/` | Stylesheet, page scripts, and the figures in `viz/` |
| `lean/Export.lean` | Exports signatures, docstrings, axioms, ranges and dependencies |
| `scripts/extract.mjs` | Collects `.ilean` data and the export into `build/lean-data.json` |
| `scripts/build.mjs`, `scripts/lean-html.mjs` | Static site generator and Lean highlighter |
| `test/geom.test.mjs` | Checks the geometry of the figures against consequences of the definitions |

## Writing

Chapters are Markdown with KaTeX math (`$…$`, `$$…$$`) and these additions.

- `@decl Name …` on its own line shows the compiled source of declarations. The first occurrence is the declaration's home, which every link to it targets. `@stmt Name` collapses the proof behind a toggle.
- `[[Name]]` or `[[Name|text]]` is an inline hoverable reference.
- Names may be fully qualified or an unambiguous suffix. The two abstract files define several names twice, so write `SourceAbstract.Mesh` or `CapAbstract.Mesh`.
- Only declarations of `*.Abstract` modules can be quoted or linked; the build fails otherwise. Write internal names as plain code.
- `@viz kind {json}` mounts the figure `src/assets/viz/<kind>.js`.
- Links whose text is `Chapter N`, `Section N.M`, `Part I` or `Appendix X` are renumbered from their target, so the number in the source does not matter.
- `::: check` ("Reading the Lean"), `::: caveat`, `::: note Title`, `::: details Title` are callouts.
- A fenced block ```` ```headline id ```` states a main result: header lines `title:`, `source:` (citation keys), `key: yes`, `theorems:` (Lean names, each also shown with `@decl` or `@stmt`), optional `skip: Name | reason`; then a blank line and the statement in English. The build computes the reading path of each headline.
- Citations are `[@key]`, `[@a; @b]`, `[@key, Theorem 3]`, `[-@key]` or `@key`. Every entry of `bibliography.json` must be cited, and its DOI or arXiv identifier checked with `npm run verify:bib`.
- `@claims`, `@audit`, `@index` and `@bibliography` generate the lists of the checking page and the appendices.

## Adding an abstract file

Add its module to `ROOTS` in `scripts/extract.mjs` and to the imports of
`lean/Export.lean`, write its chapters, and list them in `src/book.json`. The
build warns about declarations of the reading interface that no chapter shows.
