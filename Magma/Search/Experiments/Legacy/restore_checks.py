from pathlib import Path

rfc = Path('Magma/RFC8891.lean')
s = rfc.read_text()
# Restore only the actual RFC examples, not obsolete alternative proofs.
lines = s.splitlines(keepends=True)
out = []
i = 0
while i < len(lines):
    if lines[i].startswith('-- example'):
        while i < len(lines) and lines[i].startswith('-- '):
            out.append(lines[i][3:].replace('native_decide', 'decide +kernel'))
            i += 1
    elif lines[i].startswith('-- /--'):
        j = i
        while j < len(lines) and lines[j].startswith('-- '):
            j += 1
        if any(l.startswith('-- example') for l in lines[i:j]):
            out.extend(l[3:].replace('native_decide', 'decide +kernel') for l in lines[i:j])
            i = j
        else:
            out.append(lines[i]); i += 1
    else:
        out.append(lines[i]); i += 1
s = ''.join(out)
anchor = '''private def rfcDecryptState (i : Fin 32) :'''
check = '''/-- Appendix A.4: initial plaintext halves. -/
example :
    rfcEncryptState 0 =
      split 32 32 0xfedcba9876543210#64 := by
  decide

'''
assert anchor in s
s = s.replace(anchor, check + anchor)
rfc.write_text(s)

p = Path('Magma/CryptoProperties.lean')
s = p.read_text()
start = s.index('-- /-- Appendix A.4: initial plaintext halves.')
end = s.index('/-- Four-bit input/output masks', start)
s = s[:start] + s[end:]
s = s.replace('-- example :', 'example :')
p.write_text(s)

p = Path('Magma/FastSearch.lean')
s = p.read_text()
s = s.replace('validate accepted results.\n', '''validate accepted results.

Slow research recipes use `#check (expression : expectedType)` so they remain
elaborated without execution. `#guard_msgs (drop info)` suppresses only the
printed type; errors still fail the build. Replace `#check` with `#eval` to run
one recipe. Historical outputs below belong to earlier evaluations.
''')
old = '''-- Manual experiment: an earlier run exceeded ten minutes; no result was recorded.
-- #eval (generateBitDeletionCertificate (0#32) (0#32)
--   (1#32) (1#32) (0#32) 256).isSome
-- #eval scanThreeRoundBitDeletionCandidates
--   (0#32) (0#32) 256 exampleBitDeletionCandidates'''
new = '''-- Typechecked only: an earlier evaluation exceeded ten minutes; no result was recorded.
#guard_msgs (drop info) in
#check ((generateBitDeletionCertificate (0#32) (0#32)
  (1#32) (1#32) (0#32) 256).isSome : Bool)

#guard_msgs (drop info) in
#check (scanThreeRoundBitDeletionCandidates
  (0#32) (0#32) 256 exampleBitDeletionCandidates :
    Option ((V 32 × V 32 × V 32) × BitDeletionCertificate))'''
assert old in s
s = s.replace(old,new)
old = '''-- Manual bounded experiments; no outputs were recorded for these calls:
-- #eval (generateBatchedBitDeletionCertificate
  -- (0#32) (0#32) (1#32) (1#32) (0#32) 8).isSome
-- #eval groupedContradiction
--   (0#32) (0#32) (1#32) (1#32) (0#32) 2'''
new = '''-- Typechecked bounded experiments; no evaluation outputs were recorded.
#guard_msgs (drop info) in
#check ((generateBatchedBitDeletionCertificate
  (0#32) (0#32) (1#32) (1#32) (0#32) 8).isSome : Bool)

#guard_msgs (drop info) in
#check (groupedContradiction
  (0#32) (0#32) (1#32) (1#32) (0#32) 2 : Bool)'''
assert old in s
s = s.replace(old,new)
old = '''/-
  Manual experiment with a larger wave bound; no completed output was recorded:
  #eval (generateUInt16DeletionCertificate
    (0#32) (0#32) (1#32) (1#32) (0#32) 128).isSome
-/'''
new = '''-- Typechecked larger-wave experiment; no completed evaluation was recorded.
#guard_msgs (drop info) in
#check ((generateUInt16DeletionCertificate
  (0#32) (0#32) (1#32) (1#32) (0#32) 128).isSome : Bool)'''
assert old in s
s = s.replace(old,new)
# Turn recipe blocks into comments interleaved with checked terms, retaining transcripts.
def activate_block(text, start, end, terms):
    a = text.index(start)
    b = text.index(end,a) + len(end)
    block = text[a:b]
    for term, ty in terms:
        assert term in block, term
        block = block.replace(term, '-/\n#guard_msgs (drop info) in\n#check (' + term.removeprefix('  #eval ') + ' : ' + ty + ')\n/-', 1)
    return text[:a]+block+text[b:]
s = activate_block(s, '/-\n  Manual profiling recipes.', '\n-/', [
('  #eval profileUInt16Certificate\n    (0#32) (0#32) (1#32) (1#32) (0#32) 1 false', 'IO Unit'),
('  #eval profileUInt16Certificate\n    (0#32) (0#32) (1#32) (1#32) (0#32) 1 true', 'IO Unit'),
('  #eval (generateUInt16CertificateEarlyReject\n    (0#32) (0#32) (1#32) (1#32) (0#32) 8).isSome', 'Bool')])
s = activate_block(s, '/-\n  Historical initialization experiments.', '\n-/', [
('  #eval profileFastInitialCertificate\n    (0#32) (0#32) (1#32) (1#32) (0#32) 1 false', 'IO Unit'),
('  #eval fastInitialDomainsAgree (0#32) (0#32) (1#32) (0#32)', 'Bool'),
('  #eval (generateFastInitialCertificate\n    (0#32) (0#32) (1#32) (1#32) (0#32) 8).isSome', 'Bool')])
s = activate_block(s, '/-\n  Historical propagation transcript.', '\n-/', [
('  #eval fastSboxCarrySmokeTest', 'Bool'),
('  #eval profileGlobalCarryPropagation\n    (0#32) (0#32) (1#32) (1#32) (0#32) 16', 'IO Unit')])
s = s.replace('  Manual profiling recipes. No historical transcript', '  Typechecked profiling recipes (no execution). No historical transcript')
p.write_text(s)

p = Path('Magma/Evidence/ThreeRoundImpossible.lean')
s = p.read_text()
s = activate_block(s, '/-\n  Historical profiling transcript;', '\n-/', [
('  #eval Magma.Evidence.ThreeRoundImpossible.profileCheckedCarryReduction', 'IO Unit'),
('  #eval Magma.Evidence.ThreeRoundImpossible.testCarryGroupedCertificate', 'Bool')])
s = s.replace('  Historical profiling transcript; elapsed times are observations from',
'''  The following recipes are typechecked without execution; replace `#check`
  with `#eval` to run them. Only type information is suppressed by the guard.
  Historical profiling transcript; elapsed times are observations from''')
p.write_text(s)

p = Path('test.lean')
s = p.read_text()
a = s.index('/-\n  Manual research checks')
b = s.index('\nend FastInitialCheck',a)
s = s[:a] + '''/-
  These recipes are typechecked without execution on each elaboration of this
  scratch file. Replace `#check` with `#eval` to run one; the guards suppress
  only type information, not errors.
-/
#guard_msgs (drop info) in
#check (Magma.Certificates.FastInitialCheck.profileFastInitialCoverBySteps : IO Unit)
/-
  Recorded output from the previous project check:
  [initial-fast] accepted=true; time=7829ms
  The elapsed time is historical and environment-dependent.
-/

#guard_msgs (drop info) in
#check (Magma.Certificates.FastInitialCheck.testCarryGroupedCertificateFastInit : Bool)

-- Establish acceptance with a kernel-checked equality, independently of diagnostic output.
set_option maxHeartbeats 0 in
example : Magma.Certificates.FastInitialCheck.testCarryGroupedCertificateFastInit = true := by
  decide +kernel
''' + s[b:]
p.write_text(s)

p = Path('README.md')
s = p.read_text().replace('Profiling recipes remain opt-in.', '''Slow search and profiling recipes stay active as `#check (expression : expectedType)`.
This checks their types without running them. The surrounding `#guard_msgs (drop info)`
suppresses the printed type while preserving errors. Replace `#check` with `#eval` to run
an individual recipe. RFC test vectors and small component examples remain actual proofs.

Profiling execution remains opt-in.''')
s = s.replace('opt-in, since elaborating that file would rerun an active `#eval` each time.',
'''opt-in. Its concrete certificate acceptance example is an active kernel-checked proof.''')
p.write_text(s)
