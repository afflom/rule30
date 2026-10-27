#!/bin/bash
# usage: mk.sh Module   (compiles /home/claude/rule30-bridge/Module.lean to olean with 4.35)
export PATH=/tmp/claude-0/-home-claude/d0c79108-b678-53eb-ab45-e3ea4e293ad8/scratchpad/lean-4.35.0-linux/bin:$PATH
cd /home/claude/rule30-bridge
m=$1
lake env lean -o .lake/build/lib/lean/$m.olean -i .lake/build/lib/lean/$m.ilean $m.lean
