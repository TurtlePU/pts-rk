# Weak normality of canonical SK compilation

Owned NEW SKCanonicalNormal.agda only. Final module has 97 lines; source
copy under source/ and hash in final-source.sha256. No existing module,
paper, registration, index or commit edited for this subtask.

All checks use Agda 2.8.0-3d04bac at
/tmp/pts-rk-agda-2.8.0.MvVO53/agda, pinned Cubical v0.9 revision
b150186d2544e7efeddd31e5d14a8b9ecbb100f7, and isolated
AGDA_DIR=/tmp/pts-rk-sk-canonical-normal.7ItOho/config and
XDG_DATA_HOME=/tmp/pts-rk-sk-canonical-normal.7ItOho/data.
Commands preserve actual compiler exits and UTC timestamps separately.

- check01.log: --safe --no-default-libraries, exit 42. Generic caseVar
  required an explicit family parameter to disambiguate the Nf output type.
- check02.log: same flags, exit 0, zero warnings after that annotation.
- final-check.log: --safe --no-default-libraries --ignore-interfaces,
  exit 0, zero warnings, with compiled-identity executable regression added.

Exact final command:

```sh
AGDA_DIR=/tmp/pts-rk-sk-canonical-normal.7ItOho/config XDG_DATA_HOME=/tmp/pts-rk-sk-canonical-normal.7ItOho/data /tmp/pts-rk-agda-2.8.0.MvVO53/agda --safe --no-default-libraries --ignore-interfaces -i /tmp/pts-rk-sk-canonical-normal.7ItOho/source -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical /tmp/pts-rk-sk-canonical-normal.7ItOho/source/SKCanonicalNormal.agda
```

Final source stability passes. Whitespace check `git diff --no-index --check
/dev/null <source>` has empty output and exit 1, expected because no-index
implies diff's exit-code mode and the entire file is new. Safety scan has
empty output/exit 1 (no matches). Both exact exits are recorded.

Public compiled-normal takes a closed intrinsic source plus its genuine
native-normality certificate and returns an actual Core.Nf whose erasure
is the compiled SK term. This does not assume output normality: structural
bracket compilation constructs it. compiled-irreducible then applies the
independent weak-SK irreducibility theorem. The module does not depend on
SKCanonical or assume its correctness; the root can instantiate it with
the source normalizer's already-proved native-normal result.
