# Canonical substitution and material deduction — 2026-10-14

HEAD 3454c9f unchanged. Existing edits and user logs/ are preserved.
Work is uncommitted/unpushed. This is NOT a completed model soundness proof.

## Environment and baseline

Repository-root commands use:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/CanonicalTypeWitnesses.vo ZFC_model/CanonicalDenotation.vo ZFC_model/RealizationInduction.vo ZFC_model/RootBeta.vo > /tmp/pts-rk-canonical-continuation-baseline.log 2>&1
```

Baseline exit 0. Compiler versions are retained in versions.log.

## Isolated compilation history

All failed attempts are retained. No failures or resource timeouts were
converted into success. The following Bash arrays abbreviate the EXACT
repeated mapping arguments; the attempt number N identifies the retained
raw logfile, not a loop rerunning historical source revisions.

```sh
canonical_previous=/tmp/pts-rk-canonical-coherence-fresh.KhkkaT/default
canonical_ztt=(-Q "$canonical_previous/vendor/zfc" ZFC -Q "$canonical_previous/theories" PTSrk -Q "$canonical_previous/ZFC_model" PTSrkModel)
canonical_ttz=(-Q "$canonical_previous/theories" PTSrk -Q "$canonical_previous/ZFC_model" PTSrkModel -Q "$canonical_previous/vendor/zfc" ZFC)
canonical_rename=(-Q /tmp/pts-rk-canonical-renaming.S9eHKZ PTSrkModel)
canonical_realize=(-Q /tmp/pts-rk-canonical-realization.GrGIYr PTSrkModel)
canonical_substitute=(-Q /tmp/pts-rk-canonical-substitution.ORCKf9 PTSrkModel)
canonical_root=(-Q /tmp/pts-rk-canonical-root-beta.SVKjg5 PTSrkModel)
```

Temporary output directories were allocated with mktemp -d. For copied
sources, cp was executed before EACH compile attempt. Later attempts used
the revised source; earlier revisions' compiler diagnostics are preserved.

### Renaming

N=1: exit 0, six closed reports. Source comparison and recursive kernel
audit exit 0.

```sh
cp ZFC_model/CanonicalRenaming.v /tmp/pts-rk-canonical-renaming.S9eHKZ/CanonicalRenaming.v
opam exec --switch=pts-rk-ci -- timeout 120 rocq c "${canonical_ttz[@]}" "${canonical_rename[@]}" /tmp/pts-rk-canonical-renaming.S9eHKZ/CanonicalRenaming.v > /tmp/pts-rk-canonical-renaming-1.log 2>&1
cmp ZFC_model/CanonicalRenaming.v /tmp/pts-rk-canonical-renaming.S9eHKZ/CanonicalRenaming.v
opam exec --switch=pts-rk-ci -- timeout 120 rocq check -silent -o "${canonical_ttz[@]}" "${canonical_rename[@]}" PTSrkModel.CanonicalRenaming > /tmp/pts-rk-canonical-renaming-kernel.log 2>&1
```

### Realization

N=1,2: exits 0,0 (ten, then fourteen closed reports after additional
local rules). Final source comparison and recursive kernel audit exit 0.

```sh
cp ZFC_model/CanonicalRealization.v /tmp/pts-rk-canonical-realization.GrGIYr/CanonicalRealization.v
opam exec --switch=pts-rk-ci -- timeout 120 rocq c "${canonical_ttz[@]}" "${canonical_rename[@]}" "${canonical_realize[@]}" /tmp/pts-rk-canonical-realization.GrGIYr/CanonicalRealization.v > /tmp/pts-rk-canonical-realization-N.log 2>&1
cmp ZFC_model/CanonicalRealization.v /tmp/pts-rk-canonical-realization.GrGIYr/CanonicalRealization.v
opam exec --switch=pts-rk-ci -- timeout 120 rocq check -silent -o "${canonical_ttz[@]}" "${canonical_rename[@]}" "${canonical_realize[@]}" PTSrkModel.CanonicalRealization > /tmp/pts-rk-canonical-realization-kernel.log 2>&1
```

### Substitution

N=1,2: exits 1,0; dependent Fin elimination needed explicit constructor
patterns. Seven closed reports. The compiler read the repository source
directly, writing only to the temporary directory. Final fresh source
comparisons and combined recursive kernel audit cover this module.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 rocq c "${canonical_ztt[@]}" "${canonical_rename[@]}" "${canonical_substitute[@]}" -o /tmp/pts-rk-canonical-substitution.ORCKf9/CanonicalSubstitution.vo ZFC_model/CanonicalSubstitution.v > /tmp/pts-rk-canonical-substitution-N.log 2>&1
```

### Root beta

N=1,2,3,4,5: exits 1,1,0,1,0. First attempts fixed an explicit scope
argument and missing PeanoNat import; attempt 4 needed explicit lemma
arguments rather than premature inference. Final six closed reports.

Attempts 1–3 omitted the rename/realize/substitute mappings (those lemmas
had not yet been added). Attempts 4–5 used:

```sh
cp ZFC_model/CanonicalRootBeta.v /tmp/pts-rk-canonical-root-beta.SVKjg5/CanonicalRootBeta.v
opam exec --switch=pts-rk-ci -- timeout 180 rocq compile -time "${canonical_ztt[@]}" "${canonical_rename[@]}" "${canonical_realize[@]}" "${canonical_substitute[@]}" "${canonical_root[@]}" /tmp/pts-rk-canonical-root-beta.SVKjg5/CanonicalRootBeta.v > /tmp/pts-rk-canonical-root-beta-N.log 2>&1
cmp ZFC_model/CanonicalRootBeta.v /tmp/pts-rk-canonical-root-beta.SVKjg5/CanonicalRootBeta.v
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o "${canonical_ztt[@]}" "${canonical_rename[@]}" "${canonical_realize[@]}" "${canonical_substitute[@]}" "${canonical_root[@]}" PTSrkModel.CanonicalRootBeta > /tmp/pts-rk-canonical-root-beta-kernel.log 2>&1
```

Final source comparison and kernel check exit 0.

### Context transport

N=1: exit 0, seven closed reports. Source comparison and kernel audit exit 0.

```sh
cp ZFC_model/CanonicalContext.v /tmp/pts-rk-canonical-context.odv7kS/CanonicalContext.v
opam exec --switch=pts-rk-ci -- timeout 120 rocq c "${canonical_ttz[@]}" "${canonical_rename[@]}" "${canonical_realize[@]}" -Q /tmp/pts-rk-canonical-context.odv7kS PTSrkModel /tmp/pts-rk-canonical-context.odv7kS/CanonicalContext.v > /tmp/pts-rk-canonical-context-1.log 2>&1
cmp ZFC_model/CanonicalContext.v /tmp/pts-rk-canonical-context.odv7kS/CanonicalContext.v
opam exec --switch=pts-rk-ci -- timeout 120 rocq check -silent -o "${canonical_ttz[@]}" "${canonical_rename[@]}" "${canonical_realize[@]}" -Q /tmp/pts-rk-canonical-context.odv7kS PTSrkModel PTSrkModel.CanonicalContext > /tmp/pts-rk-canonical-context-kernel.log 2>&1
```

### Application

N=1,2,3,4,5: exits 1,1,1,1,0. First two corrected context inference for
realizes_membership; next two identified missing Preservation import for wf.
Final three closed reports; source comparison and kernel audit exit 0.

```sh
cp ZFC_model/CanonicalApplication.v /tmp/pts-rk-canonical-application.wdJPTz/CanonicalApplication.v
opam exec --switch=pts-rk-ci -- timeout 120 rocq c "${canonical_ttz[@]}" "${canonical_rename[@]}" "${canonical_realize[@]}" "${canonical_substitute[@]}" -Q /tmp/pts-rk-canonical-application.wdJPTz PTSrkModel /tmp/pts-rk-canonical-application.wdJPTz/CanonicalApplication.v > /tmp/pts-rk-canonical-application-N.log 2>&1
cmp ZFC_model/CanonicalApplication.v /tmp/pts-rk-canonical-application.wdJPTz/CanonicalApplication.v
opam exec --switch=pts-rk-ci -- timeout 120 rocq check -silent -o "${canonical_ttz[@]}" "${canonical_rename[@]}" "${canonical_realize[@]}" "${canonical_substitute[@]}" -Q /tmp/pts-rk-canonical-application.wdJPTz PTSrkModel PTSrkModel.CanonicalApplication > /tmp/pts-rk-canonical-application-kernel.log 2>&1
```

### Hereditary application at rank one

N=1: exit 0, four closed reports; source comparison and kernel audit exit 0.

```sh
cp ZFC_model/CanonicalHereditary.v /tmp/pts-rk-canonical-hereditary.u3RUGU/CanonicalHereditary.v
opam exec --switch=pts-rk-ci -- timeout 180 rocq compile -time "${canonical_ztt[@]}" "${canonical_rename[@]}" "${canonical_realize[@]}" "${canonical_substitute[@]}" "${canonical_root[@]}" -Q /tmp/pts-rk-canonical-hereditary.u3RUGU PTSrkModel /tmp/pts-rk-canonical-hereditary.u3RUGU/CanonicalHereditary.v > /tmp/pts-rk-canonical-hereditary-1.log 2>&1
cmp ZFC_model/CanonicalHereditary.v /tmp/pts-rk-canonical-hereditary.u3RUGU/CanonicalHereditary.v
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o "${canonical_ztt[@]}" "${canonical_rename[@]}" "${canonical_realize[@]}" "${canonical_substitute[@]}" "${canonical_root[@]}" -Q /tmp/pts-rk-canonical-hereditary.u3RUGU PTSrkModel PTSrkModel.CanonicalHereditary > /tmp/pts-rk-canonical-hereditary-kernel.log 2>&1
```

### Material first-order theory

N=1,2,3,4: exits 1,0,0,0. First attempt needed explicit dependent
constructor patterns. Later successful revisions added the bounded
embedding/schema, then its actual Ens satisfaction proof. Final eleven
closed reports. This compiler reads the repository source directly.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 rocq c "${canonical_ztt[@]}" -Q /tmp/pts-rk-material-theory.1cekfo PTSrkModel -o /tmp/pts-rk-material-theory.1cekfo/MaterialSetTheory.vo ZFC_model/MaterialSetTheory.v > /tmp/pts-rk-material-set-theory-N.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o "${canonical_ztt[@]}" -Q /tmp/pts-rk-material-theory.1cekfo PTSrkModel PTSrkModel.MaterialSetTheory > /tmp/pts-rk-material-set-theory-separation-kernel.log 2>&1
```

Kernel exit 0. The earlier kernel command after attempt 3 was identical
except its logfile was pts-rk-material-set-theory-kernel.log; exit 0 too.

## Integrated, fresh and complete CI builds

The first integrated build (before application/hereditary and final
material schema-satisfaction extension) exited 0:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/CanonicalRootBeta.vo ZFC_model/CanonicalContext.vo ZFC_model/MaterialSetTheory.vo ZFC_model/RealizationInduction.vo > /tmp/pts-rk-canonical-substitution-integrated-1.log 2>&1
```

The following fresh directory was allocated with mktemp -d, then:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-canonical-substitution-fresh.lltB68 --display=short --no-buffer ZFC_model/CanonicalRenaming.vo ZFC_model/CanonicalRealization.vo ZFC_model/CanonicalSubstitution.vo ZFC_model/CanonicalRootBeta.vo ZFC_model/CanonicalContext.vo ZFC_model/CanonicalApplication.vo ZFC_model/CanonicalHereditary.vo ZFC_model/MaterialSetTheory.vo ZFC_model/RealizationInduction.vo ZFC_model/RootBeta.vo > /tmp/pts-rk-canonical-substitution-fresh.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/canonical-substitution-final" bash tools/check-local-ci.sh > /tmp/pts-rk-canonical-substitution-ci.log 2>&1
for model_module in CanonicalRenaming CanonicalRealization CanonicalSubstitution CanonicalRootBeta CanonicalContext CanonicalApplication CanonicalHereditary MaterialSetTheory; do
  cmp "ZFC_model/$model_module.v" "/tmp/pts-rk-canonical-substitution-fresh.lltB68/default/ZFC_model/$model_module.v" || exit "$?"
done
```

Fresh build, all eight source comparisons and CI exited 0. All 161 CI
stages passed, including pristine upstream; no CI weakening. Fresh build
printed 397 closed reports across its selected dependencies, including
58 in the eight new modules. No final build timed out.

## Recursive kernel and exact theorem-type audit

```sh
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-canonical-substitution-fresh.lltB68/default/vendor/zfc ZFC -Q /tmp/pts-rk-canonical-substitution-fresh.lltB68/default/theories PTSrk -Q /tmp/pts-rk-canonical-substitution-fresh.lltB68/default/ZFC_model PTSrkModel PTSrkModel.CanonicalRenaming PTSrkModel.CanonicalRealization PTSrkModel.CanonicalSubstitution PTSrkModel.CanonicalRootBeta PTSrkModel.CanonicalContext PTSrkModel.CanonicalApplication PTSrkModel.CanonicalHereditary PTSrkModel.MaterialSetTheory PTSrkModel.RealizationInduction PTSrkModel.RootBeta > /tmp/pts-rk-canonical-substitution-kernel.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 rocq c -Q /tmp/pts-rk-canonical-substitution-fresh.lltB68/default/vendor/zfc ZFC -Q /tmp/pts-rk-canonical-substitution-fresh.lltB68/default/theories PTSrk -Q /tmp/pts-rk-canonical-substitution-fresh.lltB68/default/ZFC_model PTSrkModel -o /tmp/pts-rk-canonical-substitution-audit.roIhKc/AUDIT.vo docs/direct-r-handoff/verification/canonical-substitution-2026-10-14/AUDIT.v > /tmp/pts-rk-canonical-substitution-assumptions.log 2>&1
```

Both commands exited 0. The recursive kernel summary lists only existing
functional_extensionality_dep, with no unsafe fixpoints, type-in-type or
assumed positivity. All nine explicit assumption reports are closed.
The retained AUDIT.v prints actual theorem types and their assumptions,
including original_realization_from_conversion with its STILL UNPROVED
conversion premise. A closed assumption report does not discharge that
explicit premise or establish first-order BZC derivability.
