#!/usr/bin/env bash
# Root froze all seven modules and the aggregate before the fresh audit.
OPERATION_FROZEN=yes
OPERATION_MODULES=(NamedBeta BooleanAgreement ContextLookupCodes InternalContextLookup
  ContextLookupRealization InternalComparisonGraph ComparisonGraphRealization)
OPERATION_AUDIT=OperationProvenanceAudit
OPERATION_ALIAS=operation-provenance-audit
