#!/usr/bin/env bash

ROOT=$(cd `dirname $0` && pwd)
JSYJS="${ROOT}/node/jsy.js"

node ${JSYJS} $@
