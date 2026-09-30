# Completed helper probe archive

This append-only archive was extracted from the existing local tool transcript.
No probe was rerun during archival. It contains all 11 completed Lean stdin
invocations by late_simp_api, including 4 exit-0 and 7 exit-1 attempts.
Some failed invocations contain several example declarations; only the complete
invocation exit status is represented as pass/fail here.

Each directory contains the actual stdin source, original shell command,
explicit CLI argv, known environment override and cwd, full retained combined
compiler output, exact tool result including exit status and wall duration,
and the matching call/result transcript records. Empty output files mean the
recorded tool result contained an empty output string.

The original exec_command tool combined stdout and stderr. Separate streams,
inherited environment, actual OS wrapper/shell argv, and CPU time were not
retained and are explicitly marked unavailable in each record.json. The CLI
argv lake/env/lean/--stdin and LEAN_NUM_THREADS=1 override are taken directly
from each original command. No missing details were recreated.

The icc_api helper archives its own calls in the sibling icc-api directory.
