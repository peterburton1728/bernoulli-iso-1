from pathlib import Path
import hashlib
import sys
sys.set_int_max_str_digits(100000)
# Usage: python3 generate_certificate.py OUTPUT_PATH
# Python 3.11+ is required for the integer-to-decimal conversion limit setting.
if len(sys.argv) != 2:
    raise SystemExit('usage: generate_certificate.py OUTPUT_PATH')
out = Path(sys.argv[1])
p = 21701
q = (1 << p) - 1
blocksize = 64
steps = p - 2
lines = [
'module',
'',
'public import Mathlib.NumberTheory.LucasLehmer',
'',
'@[expose] public section',
'',
'set_option exponentiation.threshold 22000',
'set_option maxRecDepth 10000',
'',
'/-! A Lucas–Lehmer certificate with bounded kernel reduction at each checkpoint.',
'',
'Every block is checked by reflexivity. The opaque checkpoint theorems connect',
'blocks using an abstract composition law, so an independent kernel does not',
'need to reduce all 21699 iterations in a single definitional equality.',
'The decimal residues are generated data; their correctness is established by',
'each block theorem, rather than trusted from the generator. -/',
'',
'namespace BernoulliIso.CheckpointPrimeCertificate',
'',
'open LucasLehmer.norm_num_ext',
'',
'private abbrev modulus : ℕ := 2 ^ 21701 - 1',
'',
'private theorem go_add (q m n b : ℕ) :',
'    sModNatTR.go q (m + n) b = sModNatTR.go q n (sModNatTR.go q m b) := by',
'  induction m generalizing b with',
'  | zero => simp only [Nat.zero_add, sModNatTR.go]',
'  | succ m ih =>',
'    simpa only [Nat.succ_add, sModNatTR.go] using',
'      (ih ((b ^ 2 + (q - 2)) % q))',
'',
'private theorem initial : 4 % modulus = 4 := rfl',
'']
r = 4
prev_count = 0
for i, start in enumerate(range(0, steps, blocksize)):
    n = min(blocksize, steps - start)
    before = r
    for _ in range(n):
        r = (r*r - 2) % q
    total = start + n
    lines += [
        f'private theorem block_{i:03d} :',
        f'    sModNatTR.go modulus {n} {before} =',
        f'      {r} := rfl',
        '',
        f'private theorem checkpoint_{i:03d} :',
        f'    sModNatTR.go modulus {total} 4 =',
        f'      {r} :=']
    if i == 0:
        lines += [f'  block_{i:03d}']
    else:
        lines += [
            f'  (go_add modulus {prev_count} {n} 4).trans',
            f'    ((congrArg (sModNatTR.go modulus {n}) checkpoint_{i-1:03d}).trans block_{i:03d})']
    lines += ['']
    prev_count = total
assert r == 0, 'Lucas–Lehmer certificate does not end at zero'
lines += [
'/-- The original Lucas–Lehmer proposition, assembled from the checked blocks. -/',
' theorem lucasLehmerTest : LucasLehmer.LucasLehmerTest 21701 := by',
'  apply testTrueHelper 21701 rfl',
'  exact (congrArg (sModNatTR.go modulus 21699) initial).trans checkpoint_339',
'',
'/-- The same prime certificate as in the submitted construction. -/',
' theorem mersenne_prime : (mersenne 21701).Prime :=',
'  lucas_lehmer_sufficiency 21701 (by decide) lucasLehmerTest',
'',
'end BernoulliIso.CheckpointPrimeCertificate',
'']
out.write_text('\n'.join(lines))
print(f'{out}: {len(lines)} lines, {out.stat().st_size} bytes')
print(f'SHA256 {hashlib.sha256(out.read_bytes()).hexdigest()}')
