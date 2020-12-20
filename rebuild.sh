#!/bin/bash
set -e
coqc -Q . iVM Init.v
coqc -Q . iVM DSet.v
coqc -Q . iVM Mixer.v
coqc -Q . iVM Lens.v
coqc -Q . iVM Restr.v
coqc -Q . iVM Mon.v
coqc -Q . iVM Binary.v
coqc -Q . iVM Operations.v
coqc -Q . iVM OpCodes.v
coqc -Q . iVM Machine.v
coqc -Q . iVM Rel.v
coqc -Q . iVM StateRel.v
coqc -Q . iVM Mono.v
coqc -Q . iVM Cert0.v
coqc -Q . iVM Cert.v
