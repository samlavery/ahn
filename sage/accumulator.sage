#!/usr/bin/env sage
################################################################
import secrets
import os
import random
import hashlib
import base64
import pickle
from binascii import hexlify
#sage --pip install pycryptodome
from Crypto.Cipher import AES
from Crypto.Random import get_random_bytes
from Crypto.Util.Padding import pad,unpad

n = 128
rnds=3
r=1
data_count = 20
ps = [257, 133733557800380723707235713, 3674486483990229966264985502154881, 277607387889041068344634698360622849,
      46892497174283636007114170355627877121, 3001732422913219376338819698366525492620301042048305923969,
      118744335938510172901865837048012915675869744546731752058788813398407843194772622919696372887588295330577087836583448696260068152634969521002231254822337254541535132698518177689925659970852178836369012022087730057974652696089279343672884959353530300970377497055352552029394498292200388494575562951764022805633]

ws = [9, 64067737555402157637662896, 1890847646321174403442558538216985, 36911849899402943224960606644039613,
       37253208155173144133957004832098928, 398896133189425383704948920182858832658280341425750379731,
       36002204750701367682167503858431975288611365165428673275384176473544617011989694950905175427663078583807739301641059176913579991093639603890201181504799231631696635098865383517824339544490536338747075777300983867512934022650916857434847522334109816089123127667318268160541213613969798684872801298003997245812]


################################################################

# helper functions---implemented differently for simplicity,
# notably using a non-cryptographic RNG instead of an XOF!
# (this shouldn't affect correctness, only security)

def PolyVecToBin(Y):
    return b''.join(map(CoeffToBin, Y))
def CoeffToBin(c, cs=128):
    return int(c).to_bytes(cs)
def ParseBits(b):
    return ZZ.from_bytes(c)

def BinToPolyVec(B, cs):
    assert len(B) == n * cs
    return tuple(ParseBits(B[i:i+cs]) for i in range(0,len(B),cs))

def GenRelatedPoly(Y, bound=ps[0]):
    from hashlib import sha256
    from random import Random
    seed = sha256(PolyVecToBin(Y)).digest()
    rng = Random(seed)
    return tuple(ZZ(rng.randrange(bound)) for _ in range(n))

def RootGen(Y, l, r):
    from hashlib import sha256
    from random import Random
    seed = sha256(PolyVecToBin(Y) + PolyVecToBin(Y)).digest()
    rng = Random(seed)
    return tuple(ZZ(rng.randrange(-r, r+1)) for _ in range(l))

################################################################

# NTT functions (copied from paper)

def pointwise_addition(vec1, vec2, modulus):
    return [(x + y) % modulus for x, y in zip(vec1, vec2)]

def ntt_inverse(a, MODULUS,ROOT_OF_UNITY, original_n=128):
    n = len(a)
    if n == 1:
        return a
    # Use original_n for normalization factor inv_n, which should be calculated once.
    inv_n = pow(original_n, MODULUS - 2, MODULUS)
    root_inv = pow(ROOT_OF_UNITY, (MODULUS - 1) - (MODULUS - 1) // n, MODULUS)
    w_inv = 1
    y0 = ntt_inverse(a[::2], MODULUS, ROOT_OF_UNITY, original_n=original_n)
    y1 = ntt_inverse(a[1::2],  MODULUS, ROOT_OF_UNITY, original_n=original_n)
    y = [0] * n
    for k in range(n // 2):
        y[k] = (y0[k] + w_inv * y1[k]) % MODULUS
        y[k + n // 2] = (y0[k] - w_inv * y1[k]) % MODULUS
        w_inv = (w_inv * root_inv) % MODULUS
    # Apply normalization with the correct inv_n, only once, not in recursive calls
    return [(x * inv_n) % MODULUS for x in y] if n == original_n else y


def ntt(a,  MODULUS, ROOT_OF_UNITY, depth=0):
    n = len(a)
    if n == 1:
       return a
    w = 1
    root = pow(ROOT_OF_UNITY, (MODULUS - 1) // n, MODULUS)
    a0 = ntt(a[::2],  MODULUS, ROOT_OF_UNITY,depth+1)
    a1 = ntt(a[1::2],  MODULUS, ROOT_OF_UNITY,depth+1)
    y = [0] * n
    for k in range(n // 2):
        y[k] = (a0[k] + w * a1[k]) % MODULUS
        y[k + n // 2] = (a0[k] - w * a1[k]) % MODULUS
        w = w * root % MODULUS
    return y

################################################################

#x - common reference
#y - secret
################################################################
def ZKVolute(x, y, y_rep=0):
    yoff = RootGen(y,len(ps),r)
    y_ = GenRelatedPoly(y)
    for i,(p,ww) in enumerate(zip(ps, ws)):
        x = ntt(x, p, ww)
        y_ = ntt(y_, p, ww)
        if  i<3:
            y = ntt(y, p, ww+yoff[i])
        else:
            y = ntt(y, p, ww)
        if i == 0:
            out = x           
        if i !=0:
            out = ntt(out, p, ww)
        if i == 1 or i == 2:
            out = pointwise_addition(out, y, p)
            out = pointwise_addition(out, y, p)        
            out = pointwise_addition(out, y, p)
            if y_rep:
                out = pointwise_addition(out, y_, p)
                out = pointwise_addition(out, y, p)        
                out = pointwise_addition(out, y_, p)
        if i >= 3:
            for _ in range(0,rnds):
                out = pointwise_addition(out, y, p)
                out = pointwise_addition(out, y, p)
                if y_rep:
                    out = pointwise_addition(out, y_, p)
    for p,w in reversed(list(zip(ps, ws))):
        out = ntt_inverse(out, p, w)
    return out
################################################################

def SplitPK(pk):
    # Splits public key into components
    pk_prime = secrets.token_bytes(32) 
    C = secrets.token_bytes(32)
    return pk_prime, C

def ProofNakedKexData(sk_A, pk_B_prime, C_B, iv, plaintext):
    tmp_ss = ZKVolute(pk_B_prime, sk_A,1)
    tmp_psi = ZKVolute(C_B, sk_A,1)
    ss_hash=hashlib.sha3_256()    
    ss_hash.update(pickle.dumps(tmp_ss))
    ss = ss_hash.digest()
    ciphertext=encrypt(plaintext.encode('utf-8'), ss, iv)
    return tmp_psi, ss, ciphertext

def VerifyNakedKexData(pi, sk_b, iv, ciphertext): 
    tmp_ss = ZKVolute(pi, sk_b, 1)
    ss_hash=hashlib.sha3_256()
    ss_hash.update(pickle.dumps(tmp_ss))
    ss = ss_hash.digest()
    plaintext = decrypt(ciphertext,ss,iv)
    return ss, plaintext

def GenerateData(count):
    outlist = []
    for _ in range(count):
       var=tuple(randrange(255) for _ in range(n))
       outlist.append(var)
    return outlist

def Accumulate(base, dataset):
    for data in dataset:
        base = ZKVolute(base, data)
    return base

def AuthAccumulate(base, dataset):
    for data in dataset:
        base = ZKVolute(base, data,1)
    return base



# MAIN
for _ in range(0,1000):
    # just pick a bunch of random inputs for testing
    sk_a = tuple(randrange(255) for _ in range(n))  # sk
    sk_b = tuple(randrange(255) for _ in range(n))  # sk
    ca = tuple(randrange(255) for _ in range(n))  # Ca
    cb = tuple(randrange(255) for _ in range(n))  # Cb
    data = GenerateData(data_count)


    #Test unauthenticated accumulator using ca as a base
    full_set = Accumulate(ca, data)
    print('Full value:', full_set)
    prove_idx = random.randrange(0, len(data))
    val = data[prove_idx]
    del data[prove_idx]

    partial_set = Accumulate(ca, data)
    check_set = Accumulate(partial_set, [val])
    assert check_set == full_set
    print("Proven membership of index:", prove_idx)

    #Test signing accumulator using the public key
    data = GenerateData(data_count)
    pk_a=ZKVolute(ca,sk_a,0) 

    #We start with a random base to accumulate into
    acc = AuthAccumulate(cb, data)

    #Create a signed version
    tmp = ZKVolute(ca,acc)
    signed = ZKVolute(tmp,sk_a)

    #Check that signed version is correct
    check = ZKVolute(pk_a, acc) 
    assert signed == check
    print("Authenticated accumulator passed")




