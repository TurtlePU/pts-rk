#!/usr/bin/env bash
# Finalize the fourth path and archive only after the root freezes workers.
HORN_WORKERS=(uniform-horn finite-raw-decoding uniform-reindex finite-raw-tables uniform-guarded-horn)
HORN_WORKER_ROOTS=(
  /tmp/pts-rk-uniform-horn.mgPTYI
  /tmp/pts-rk-finite-raw-decoding.aSN7Ui
  /tmp/pts-rk-uniform-reindex.saoh4V
  /tmp/pts-rk-finite-raw-tables.ldYIeE
  /tmp/pts-rk-uniform-guarded-horn.sjyP9e)
