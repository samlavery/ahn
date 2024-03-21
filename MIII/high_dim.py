#!/usr/bin/env python3
################################################################
from secrets import randbelow
import numpy as np
import sympy
from scipy import stats
from collections import Counter
from aux_code import *
import numpy as np
import matplotlib.pyplot as plt

################################################################
# test_runs = iterations of test to perform
# perform_stats_tests = Run extra statistical checks after main test loop
# n = vector count/poly length
# rnds = rounds
# ps = set of NTT moduli
# ws = set of NTT roots of unity
test_runs = 1000
perform_stats_tests = True
n = 1024
rnds = 6 
ps = [15361, 15361, 65537]
ws = [7, 7, 13]
################################################################


# Standard modular arithmetic
################################################################
def pointwise_addition(vec1, vec2, modulus):
    return [(x + y) % modulus for x, y in zip(vec1, vec2)]


def pointwise_multiplication(vec1, vec2, modulus):
    return [(x * y) % modulus for x, y in zip(vec1, vec2)]


# NTT functions
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


################################################################
# MAIN MARKIIU SIG FUNCTIONS
# INPUT
# sk_a: first half secret key
# sk_alt: second half of secret key
# sk_alt1: aux secret key - for randomization testing
# chal: Fiat-Shamir style challenge on a message
#
# OUTPUT
# proof_rep: a proof of possession of sk_a and sk_alt based on a reference challenge
################################################################
def ZKVolute_ProofGen(sk_a, sk_alt, sk_alt1, chal):
    sk_rep = sk_a
    sk_rep_alt = sk_alt
    sk_rep_alt1 = sk_alt1
    ca_rep = chal
    for i, (p, w) in enumerate(list(zip(ps, ws))):
        sk_rep = ntt(sk_rep, ps[i], ws[i])
        sk_rep_alt = ntt(sk_rep_alt, ps[i], ws[i])
        sk_rep_alt1 = ntt(sk_rep_alt1, ps[i], ws[i])
        ca_rep = ntt(ca_rep, ps[i], ws[i])

        if i == 0:
            st_rep = pointwise_multiplication(sk_rep_alt, sk_rep, ps[i])
            proof_rep = pointwise_multiplication(ca_rep, sk_rep, ps[i])
            proof_rep = pointwise_addition(proof_rep, ca_rep, ps[i])
            proof_rep = pointwise_multiplication(proof_rep, sk_rep_alt1, ps[i])
            proof_rep = pointwise_addition(proof_rep, ca_rep, ps[i])
            for _ in range(0, rnds):
                proof_rep = pointwise_multiplication(proof_rep, ca_rep, ps[i])
                proof_rep = pointwise_multiplication(proof_rep, st_rep, ps[i])
            proof_hld = proof_rep  # Move to non-additive carrier
        if i >= 1 and i != 0:  # Obsfucate and mix phase
            proof_rep = ntt(proof_rep, ps[i], ws[i])
            proof_hld = ntt(proof_hld, ps[i], ws[i])
            proof_rep = pointwise_addition(
                proof_rep, proof_rep, ps[i]
            )  # Inner folding and information loss
            proof_rep = pointwise_addition(proof_rep, proof_hld, ps[i])
    for i, (p, w) in enumerate(reversed(list(zip(ps, ws)))):
        if i < len(ps) - 1:
            proof_rep = ntt_inverse(proof_rep, p, w, original_n=n)
    return proof_rep


#################################################################
# INPUT
# pk_a: homomorphic public key (1st half of pk)
# pk_chal: public reference challenge (2nd half of pk)
# sig: signature
# sig_chal: Fiat-Shamir style hash to vector representation of a message
#
# OUTPUT
# True or False
################################################################
def ZKVolute_ProofVerify(pk_a, pk_chal, sig, sig_chal):
    p = ps[0]
    w = ws[0]
    sig_chal = ntt(sig_chal, p, w)
    pk_chal = ntt(pk_chal, p, w)
    # Generate f(f(a,b),c)
    chk_rep1 = pointwise_multiplication(sig_chal, pk_a, p)
    for _ in range(0, rnds):
        chk_rep1 = pointwise_multiplication(chk_rep1, sig_chal, p)

    # Generate f(f(a,c),b)
    chk_rep2 = pointwise_multiplication(pk_chal, sig, p)
    for _ in range(0, rnds):
        chk_rep2 = pointwise_multiplication(chk_rep2, pk_chal, p)

    # Check convolutional equivariance f(f(a,b),c) == f(f(a,c),b)
    if chk_rep1 == chk_rep2:
        return True
    else:
        return False


def randomness_tests(numbers):
    counts = Counter(numbers)
    # Calculate the expected count for a uniform distribution
    nn = len(numbers)
    expected_count = nn / ps[0]
    # Calculate the chi-square statistic
    chi_square = sum(
        (count - expected_count) ** 2 / expected_count for count in counts.values()
    )
    # Calculate the degrees of freedom
    degrees_of_freedom = ps[0] - 1  # Number of categories - 1
    # Calculate the p-value
    p_value = chi2.sf(chi_square, degrees_of_freedom)
    return {
        "chi_square": chi_square,
        "degrees_of_freedom": degrees_of_freedom,
        "p_value": p_value,
        "expected_count": expected_count,
    }


################################################################
# Main test loop
proofs = list()
challenges = list()
attempts = 0
if True:
    # KeyGen loop - reject weak public keys
    # Reject secret vectors and challenges that have 0 value coefficients - inefficient brute force implementation - with tolerance
    print("Starting KeyGen")
    while attempts == 0 or pk_a.count(0) != 0:
        attempts += 1
        sk_a = generate_non_zero_vector(n, ps[0])
        sk_alt = generate_non_zero_vector(n, ps[0])
        sk_alt1 = generate_non_zero_vector(n, ps[0])
        ca = generate_non_zero_vector(n, ps[0])
        pk_a = ZKVolute_ProofGen(sk_a, sk_alt, sk_alt1, ca)
        print(pk_a.count(0), attempts)
    print("Keygen completed after ", attempts, "attempts")
    for prog in range(0, test_runs):
        progBar(prog, test_runs)
        # Pick a random challenge for test
        pk_a = ZKVolute_ProofGen(sk_a, sk_alt, sk_alt1, ca)

        fs = generate_non_zero_vector(n, ps[0])  # Fiat-Shamir challenge emulation

        sig = ZKVolute_ProofGen(
            sk_a, sk_alt, sk_alt1, fs
        )  #  A proof of posession against a Fiat-Shamir style challenge
        check = ZKVolute_ProofVerify(pk_a, ca, sig, fs)  # Check equivariance
        proofs.append(sig)  # for analysis
        challenges.append(fs)
        if check == False:
            print("Failed test", ps[2])
            exit(0)
        else:
            attempts=attempts #nop

if perform_stats_tests == True:
    flat_list = [item for sublist in proofs for item in sublist]
    correlations = autocorrelation_test(flat_list, max_lag=n)
    print("Autocorrelation coefficients:", correlations)
    run_lengths = run_length_test(flat_list)
    print("Run Lengths:", run_lengths)
    sensitivity_results = sensitivity_test(ZKVolute_ProofGen, sk_a, sk_alt, sk_alt1, ca)
    print("Sensitivity Test Results (Hamming Distances):", sensitivity_results)
    randomness_results = randomness_tests(flat_list)
    print("Randomness Test Results:", randomness_results)
    pairwise_result = pairwise_comparison_test(flat_list)
    print("Pairwise Comparison Test Result:", pairwise_result)
    mutual_info = calculate_mutual_information(pk_a, ca)
    print("Mutual Information pk/ca:", mutual_info)
    print("Keygen completed after ", attempts, "attempts")

print("PASS")
