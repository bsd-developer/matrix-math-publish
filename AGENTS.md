# Agent instructions — matrix-math-publish

This repository publishes certified bounds on ω and their papers. Every result
release is a **GitHub release plus a Zenodo record**. Both are outward-facing
and effectively permanent: a published Zenodo version cannot be edited or
deleted. Follow the runbook below exactly, and get explicit human approval
before any push, tag push, release publish or Zenodo publish.

## Ground rules

- **Never publish a claim stronger than the evidence.** A certified result needs
  the complete certificate checks for its profile (CN or CK). Numerical scores
  are never called certified.
- **Keep the trust boundary explicit in every release:** standard Lean axioms,
  any native-evaluation axiom, `MatrixMath.AX1_combination_loss`, and the
  compiler/runtime/GMP TCB.
- **Preserve account details.** Releases, PDFs, Zenodo metadata, commit messages
  and artifacts must carry only the publishing account (bsd-developer) and 
  contact address (bsd.developer@proton.me). Never include other names, emails, 
  usernames, home-directory paths or machine hostnames. Normal bibliographic
  credits to cited researchers are not publishing-account identity fields.
- **Do not run long jobs (Lean CN, full Rust checks) unless the human asks.**
  Record which checks were run and which were reused.
- **Once a release is published, its files are frozen.** Corrections go in a new
  version, never in place.

## What every release must contain

Each item is required unless marked *(optional)*.

### A. Result package (`certifications/<release-id>/`, in Git)

1. `README.md`. It states:
   - the exact claim (rational) and an approximate decimal;
   - the ω definition used, for example `ω_Q` and where it is defined;
   - the certification profile;
   - a one-paragraph trust summary.
2. `trust-boundary.md`. It gives the complete axiom list, the TCB, what is
   *not* proved (for example AX1), and how to audit the AX1 transcription.
3. `verification-runbook.md`. It contains:
   - download and setup steps;
   - toolchain pins;
   - **hardware used and observed peak memory**, with an expected minimum;
   - **expected durations** per step;
   - **exact expected output** of the Rust check;
   - the comparison steps for CN output;
   - a "Trust anchors" section naming the externally printed digests.
4. `verification-source/`. The reduced, buildable Rust and Lean source, with
   `Cargo.lock`, `lake-manifest.json`, `rust-toolchain.toml` and
   `lean-toolchain`. Include:
   - the spec (`docs/specs/0001_spec.md`);
   - the relevant ADRs;
   - `docs/traceability.md`, the spec-to-Lean/Rust map needed for the AX1 audit.
5. Assurance records:
   - `compiled-assurance.json` (declaration statements, statement hashes,
     transitive axioms);
   - `assurance.json`;
   - `tcb.json`;
   - `runtime-trust-summary.json`.

   None of these may contain private filesystem paths.
6. `manifest.json`, `SHA256SUMS` and `verify-files.py`, which bind every
   package file plus the separate large assets. The manifest is excluded from
   its own inventory. `verify-files.py` must pass.
7. `paper/`, containing:
   - the source (`paper.md`);
   - the built PDF (`build/paper.pdf`);
   - `figures/`;
   - `data/` (the aggregate CSVs behind every figure, with
     `data/manifest.json`);
   - `build.sh`.

### B. Large payloads (GitHub release assets, *not* in Git)

8. The canonical certificate, `certificate.json`.
9. The generated Lean theorem, losslessly compressed (`*.lean.gz`).
10. `<release-id>-verification.tar.gz`: the package from section A, built from
    the **committed tree at the release tag**.
11. `release-assets-SHA256SUMS.txt`, with checksums for every other release asset.
    The checksum file excludes itself to avoid self-reference; its own digest
    is recorded separately in the release notes and release log.
12. *(optional)* `<release-id>-paper-data.tar.gz`, if the paper data is not
    already in the tagged tree.

### C. GitHub release

13. An **annotated, signed tag** named `<release-id>` that points at the commit
    containing sections A and the paper. Use a dedicated BSD SSH signing key
    (verified with `release-signers`), or an explicitly approved Auths identity
    with `sign_release` scope. Commits may remain unsigned.
14. Release notes with:
    - the exact claim;
    - the certificate SHA-256 and byte count;
    - the generated-module SHA-256;
    - the certification profile and axiom list;
    - a link to the paper PDF;
    - the "how to verify" commands;
    - known limitations (AX1 unproved, native evaluation, untested paths).
15. The root `README.md` results table updated for the new result.

### D. Zenodo record

16. **All files**: the four or five GitHub release assets, the paper PDF and
    `CITATION.cff`. Zenodo must hold the large payloads itself so the record is
    self-sufficient if GitHub disappears.
17. **Metadata:**
    - title matching the paper;
    - creators: the pseudonym only;
    - description: the claim, profile, axioms and certificate digest;
    - version equal to `<release-id>`;
    - publication date;
    - licence;
    - keywords.
18. **Related identifiers:**
    - the GitHub release URL (`isSupplementTo` / `isIdenticalTo` as
      appropriate);
    - the source works cited for the bridge theorem and formulation (arXiv IDs
      and DOIs), as `references`;
    - the previous version's DOI (`isNewVersionOf`).
19. The record uses the existing **concept DOI** (one per result line) and gets
    a new **version DOI** per release. Put the version DOI back into the paper,
    `CITATION.cff` and the README *before* the final PDF, or in a follow-up
    version if Zenodo integration mints it at publish time.

### E. Repository-level files (create once, keep current)

20. `LICENSE`, with separate code and text/data licences stated if they differ.
21. `CITATION.cff`, with the pseudonym, title, version, DOI and release date.
22. `papers/shared/references.bib`, which every paper cites from. Every
    citation must resolve.

## Standard release runbook

Steps marked **[approval]** need explicit human go-ahead in the current
conversation.

### 1. Freeze the result

1. Confirm the certification receipts for the claimed profile are complete:
   - producer;
   - independent exact minimum;
   - Rust XC;
   - full CN;
   - strict compiled audit and TCB;
   - replay and the four literal comparisons;
   - local closure.

   Do not release while any certification process is live.
2. Record the exact claim, certificate digest and size, and generated-module
   digest and size. These are the **trust anchors** and appear verbatim in the
   paper, the README, the release notes and the Zenodo description.

### 2. Assemble the package (section A)

3. Copy result files byte-for-byte. Mark each manifest entry's origin
   (`literal-copy`, `lossless-compression`, `package-document-or-build-wrapper`,
   `reduced-workspace-lock`).
4. Write or refresh `README.md`, `trust-boundary.md` and
   `verification-runbook.md`, including hardware, durations, expected outputs
   and the AX1 audit section.
5. Include `traceability.md`, and check that every Lean declaration it names
   exists in `verification-source/lean/`.
6. Regenerate `manifest.json` and `SHA256SUMS` in their existing format,
   preserving entry order. Then run:

   ```sh
   python3 verify-files.py
   ```

   It must print `"passed": true`. **Any edit to a package file requires
   re-running this step.**

### 3. Paper

7. Build with `bash certifications/<release-id>/paper/build.sh`.
8. Check the build output:
   - exiftool scrub reports no author, creator or producer metadata;
   - no unresolved citations (`pdftotext … | grep -E '\?\?|@[a-z]+[0-9]{4}'`
     is empty);
   - no raw `$` or LaTeX commands in the extracted text;
   - figures embedded.
9. Check the claims:
   - every number in the paper matches `data/` and the receipts;
   - cited theorems carry exact theorem and section numbers;
   - the trust boundary matches `compiled-assurance.json`.
10. The human does the visual layout review.

### 4. Privacy scan

11. Scan everything that will ship: the package, `paper/`, release notes, and
    tarball contents. The scan must find:
    - no home-directory paths (`/Users/`, `/home/`);
    - no real names, personal emails, usernames or hostnames;
    - no private worktree or checkpoint paths;
    - no secrets or tokens.

    Also check PDF and image metadata. Fix the source and rebuild if anything
    is found.

### 5. Commit and tag

12. Commit the package and paper with only the pseudonymous identity configured.
13. Create an annotated tag at that commit and sign it using the dedicated BSD
    SSH key, or an explicitly approved Auths `sign_release` identity. Never use
    another identity's existing device key. Check the signature with:

    ```sh
    git -c gpg.format=ssh -c gpg.ssh.program=ssh-keygen \
      -c gpg.ssh.allowedSignersFile=release-signers verify-tag <release-id>
    ```

    `release-signing.pub` contains only the public key; its fingerprint appears
    in the release notes. Never commit private keys. If a tag already exists from a
    draft, move it only before any public release, and say so in the notes.

### 6. Build release assets

14. Build `<release-id>-verification.tar.gz` from the tagged tree, for example
    with `git archive <release-id> certifications/<release-id>`. Extract it into
    a temporary directory, add the payloads and run `verify-files.py` there.
15. Write `release-assets-SHA256SUMS.txt` over all assets, then recheck every
    checksum.

### 7. GitHub draft release

16. **[approval]** Push the commit and tag.
17. **[approval]** Create or update the **draft** release:
    - replace every stale asset (any asset older than the last package edit is
      stale);
    - paste the release notes (item 14);
    - re-download the assets and re-verify their checksums.

### 8. Verification gate

18. Fast checks, always: `verify-files.py` on the downloaded assets; the
    certificate's head claim matches the trust anchors.
19. Full reader-path check, for the first release of a result line and whenever
    the verification source changes: a clean-room run of the runbook from the
    downloaded assets (build, Rust check, CN). Record the outcome in the release
    notes. If it has not been done, the notes and paper must say so explicitly.

### 9. Publish

20. **[approval]** Publish the GitHub release.
21. **[approval]** Create the Zenodo version. Use the GitHub integration, or a
    manual upload of all section D files. Check the files, checksums and
    metadata in the Zenodo **draft** preview. Publishing is irreversible.
22. Put the minted version DOI into `CITATION.cff`, the README and, if needed,
    a paper revision. Commit as a documentation follow-up; do not alter
    released assets.

### 10. Close out

23. Update the root `README.md` results table and `papers/` index.
24. Record the release identifiers in the release log:
    - tag and commit;
    - asset checksums;
    - DOI;
    - which verification steps were run versus reused.

## Common failure modes

- **Editing the package after uploading.** Assets become stale; the tarball
  checksum no longer matches. Rebuild assets every time.
- **Manifest self-reference.** `manifest.json` is excluded from its own
  inventory but listed last in `SHA256SUMS`. Update its checksum *after*
  writing it.
- **Untracked `paper/`.** Files not committed at the tag are missing from
  GitHub's source archive.
- **Comparing certified to displayed values.** Say "below the displayed bound"
  unless the competitor's exact value is public.
- **Calling an XC (Rust-only) check "certified".**
