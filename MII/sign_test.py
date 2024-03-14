#!/usr/bin/env python3
################################################################
from secrets import randbelow

#######
# n = degree poly
# rnds = rounds
# ps = set of NTT moduli
# ws = set of NTT roots of unity
n = 128
rnds = 4
ps = [257, 257, 257, 257, 65537, 133733557800380723707235713]
ws = [5, 8, 13, 21, 34, 55, 89]
################################################################

def ntt_inverse(a, MODULUS, ROOT_OF_UNITY, original_n=n):
    n = len(a)
    if n == 1:
        return a
    # Use original_n for normalization factor inv_n,  ich should be calculated once.
    inv_n = pow(original_n, MODULUS - 2, MODULUS)
    root_inv = pow(ROOT_OF_UNITY, (MODULUS - 1) - (MODULUS - 1) // n, MODULUS)
    w_inv = 1
    y0 = ntt_inverse(a[::2], MODULUS, ROOT_OF_UNITY, original_n=original_n)
    y1 = ntt_inverse(a[1::2], MODULUS, ROOT_OF_UNITY, original_n=original_n)
    y = [0] * n
    for k in range(n // 2):
        y[k] = (y0[k] + w_inv * y1[k]) % MODULUS
        y[k + n // 2] = (y0[k] - w_inv * y1[k]) % MODULUS
        w_inv = (w_inv * root_inv) % MODULUS
    # Apply normalization with the correct inv_n, only once, not in recursive calls
    return [(x * inv_n) % MODULUS for x in y] if n == original_n else y


def ntt(a, MODULUS, ROOT_OF_UNITY, depth=0):
    n = len(a)
    if n == 1:
        return a
    w = 1
    root = pow(ROOT_OF_UNITY, (MODULUS - 1) // n, MODULUS)
    a0 = ntt(a[::2], MODULUS, ROOT_OF_UNITY, depth + 1)
    a1 = ntt(a[1::2], MODULUS, ROOT_OF_UNITY, depth + 1)
    y = [0] * n
    for k in range(n // 2):
        y[k] = (a0[k] + w * a1[k]) % MODULUS
        y[k + n // 2] = (a0[k] - w * a1[k]) % MODULUS
        w = w * root % MODULUS
    return y


# Modular arithmetic
################################################################
def pointwise_addition(vec1, vec2, modulus):
    return [(x + y) % modulus for x, y in zip(vec1, vec2)]

def pointwise_multiplication(vec1, vec2, modulus):
    return [(x * y) % modulus for x, y in zip(vec1, vec2)]

################################################################
# MAIN MARKII SIG FUNCTIONS
def ZKVolute_ProofGen(sk_a, sk_alt, chal):
    sk_rep = sk_a
    sk_rep_alt = sk_alt
    ca_rep = chal
    for i, (p, w) in enumerate(list(zip(ps, ws))):
        sk_rep = ntt(sk_rep, ps[i], ws[i])
        sk_rep_alt = ntt(sk_rep_alt, ps[i], ws[i])
        ca_rep = ntt(ca_rep, ps[i], ws[i])
        if i == 0:
            st_rep = pointwise_multiplication(sk_rep_alt, sk_rep, ps[i])
            proof_rep = pointwise_multiplication(ca_rep, sk_rep, ps[i])
            proof_rep = pointwise_addition(proof_rep, ca_rep, ps[i])
            proof_rep = pointwise_multiplication(proof_rep, st_rep, ps[i])
            for _ in range(0, rnds):
                proof_rep = pointwise_multiplication(proof_rep, ca_rep, ps[i])
                proof_rep = pointwise_multiplication(proof_rep, sk_rep, ps[i])
            proof_rep = pointwise_multiplication(proof_rep, sk_rep_alt, ps[i])

            proof_hld = proof_rep  # Move to non-additive carrier
        if i >= 1 and i != 0:  # Obsfucate and mix phase
            proof_rep = ntt(proof_rep, ps[i], ws[i])
            proof_hld = ntt(proof_hld, ps[i], ws[i])
            st_rep = ntt(st_rep, ps[i], ws[i])

            proof_rep = pointwise_addition(proof_rep, proof_rep, ps[i])  # Inner folding and information loss
            proof_rep = pointwise_addition(proof_rep, proof_hld, ps[i])
            proof_rep = pointwise_addition(proof_rep, proof_rep, ps[i])

    for i, (p, w) in enumerate(reversed(list(zip(ps, ws)))):
        if i < len(ps) - 1:
            proof_rep = ntt_inverse(proof_rep, p, w, original_n=n)
    return proof_rep

def ZKVolute_ProofVerify(pk_a, pk_chal, sig, sig_chal):
    p = ps[0]
    w = ws[0]
    i = 0
    sig_chal = ntt(sig_chal, p, w)
    pk_chal = ntt(pk_chal, p, w)
    if i == 0:
        chk_rep1 = pointwise_multiplication(sig_chal, pk_a, p)
        for _ in range(0, rnds):
            chk_rep1 = pointwise_multiplication(chk_rep1, sig_chal, p)

        chk_rep2 = pointwise_multiplication(pk_chal, sig, p)
        for _ in range(0, rnds):
            chk_rep2 = pointwise_multiplication(chk_rep2, pk_chal, p)
        assert chk_rep1 == chk_rep2
        if chk_rep1 == chk_rep2:
            return True
        else:
            return False


# Main test loop
if True:
    sk_a = tuple(randbelow(255) for _ in range(n))  # sk
    sk_alt = tuple(randbelow(255) for _ in range(n))  # second sk
    ca = tuple(randbelow(255) for _ in range(n))  # Ca
    for yx in range(0, 100):
        # just pick a bunch of random challenges for test
        fs = tuple(randbelow(255) for _ in range(n))  # FS_Chal

        pk_a = ZKVolute_ProofGen(sk_a, sk_alt, ca)
        sig = ZKVolute_ProofGen(sk_a, sk_alt, fs)
        check = ZKVolute_ProofVerify(pk_a, ca, sig, fs)
        #print("PK:", pk_a)
        #print("SK:", sk_a)
        #print("SX:", sk_alt)
        #print("CA:", ca)
        #print("FS:", fs)
        #print("SIG:", sig)
        if check == False:
            print("Failed test")
            exit(0)
print("PASS")
