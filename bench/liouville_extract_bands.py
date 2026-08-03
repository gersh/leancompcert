import re
src = open('/home/gersh/claude_math/.claude/worktrees/agent-adeb6a379b7d76af0/'
           'MathExtras/NumberTheory/Certs/LiouvilleLittleSumSweepDefs.lean').read()
blk = src[src.index('def ellBands'):src.index('def bandsWidth') if 'def bandsWidth' in src else len(src)]
trips = re.findall(r'\((\d+),\s*(\d+),\s*(\d+)\)', blk)
with open('liouville_bands.py', 'w') as f:
    f.write("ellBands = [\n")
    for w, T, L in trips:
        f.write(f"    ({w}, {T}, {L}),\n")
    f.write("]\n")
print("bands:", len(trips), "total width:", sum(int(t[0]) for t in trips))
