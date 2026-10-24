#!/usr/bin/env bash
# Root must finalize the scope and explicitly freeze sources before launch.
HORN_FROZEN=yes
HORN_MODULES=(UniformHorn FiniteRawDecoding UniformHornReindex FiniteRawTables UniformGuardedHorn)
HORN_AUDIT=UniformHornAudit
HORN_ALIAS=uniform-horn-audit
