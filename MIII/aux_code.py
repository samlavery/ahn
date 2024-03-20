from collections import Counter
import numpy as np
import random
import secrets
from scipy.stats import chi2
from sklearn.metrics import mutual_info_score



def hamming_distance_test(output1, output2):
    assert len(output1) == len(output2), "Outputs must be of the same length"
    return hamming(output1, output2) * len(output1)

def autocorrelation_test(output_list, max_lag):
    n = len(output_list)
    correlation = [np.corrcoef(output_list[:-lag], output_list[lag:])[0, 1] for lag in range(1, max_lag)]
    return correlation

def run_length_test(sequence):
    counts = Counter()
    current, count = None, 0
    for element in sequence:
        if element == current:
            count += 1
        else:
            if current is not None:
                counts[count] += 1
            current, count = element, 1
    counts[count] += 1  # for the last run
    return counts

def progBar(iteration, total, prefix = " Running tests", suffix = ' ', decimals = 2, length = 125, fill = '█', printEnd = "\r"):
    percent = ("{0:." + str(decimals) + "f}").format(100 * (iteration / float(total)))
    filledLength = int(length * iteration // total)
    bar = fill * filledLength + '-' * (length - filledLength)
    print(f'{prefix} |{bar}| {percent}% {suffix}', end = printEnd)
    # Print New Line on Complete
    if iteration == total-1:
        filledLength = int(length * (iteration+1) // total)
        bar = fill * filledLength + '-' * (length - filledLength)
        print(f'{prefix} |{bar}| 100% {suffix}', end = "\n")
        print("\n")
def pairwise_comparison_test(sequence):
    distinct_pairs = 0
    total_pairs = 0
    for i in range(len(sequence) - 1):
        total_pairs += 1
        if sequence[i] != sequence[i + 1]:
            distinct_pairs += 1
    return distinct_pairs / total_pairs if total_pairs > 0 else 0

def calculate_entropy(coefficients):
    # Count the frequency of each coefficient
    frequency = Counter(coefficients)
    # Calculate probabilities
    probabilities = [freq / len(coefficients) for freq in frequency.values()]
    # Calculate Shannon entropy
    entropy = -sum(p * math.log2(p) for p in probabilities if p > 0)
    return entropy

def calculate_mutual_information(x, y):
    # Flatten y if it's a list of tuples
    if isinstance(y[0], tuple):
        y = np.array(y).flatten()
        x = np.array(x).flatten()
    return mutual_info_score(x, y)

def calculate_correlations(public_key, proofs):
    pearson_corr, _ = pearsonr(public_key, proofs)
    spearman_corr, _ = spearmanr(public_key, proofs)
    return pearson_corr, spearman_corr

def sensitivity_test(proof_gen_function, a,b,c,d, num_tests=100):
    differences = []
    aa = a.copy()
    bb=b.copy()
    cc=c.copy()
    dd=d.copy()
    for _ in range(num_tests):
        r = random.randrange(3) #randbelow[3]
        if r == 0:
            altered_index = random.randrange(len(a))
            a[altered_index] ^= 1  # Flip a bit
        if r == 1:
            altered_index = random.randrange(len(b))
            b[altered_index] ^= 1  # Flip a bit
        if r == 2:
            altered_index = random.randrange(len(c))
            c[altered_index] ^= 1  # Flip a bit
        original_output = proof_gen_function(aa,bb,cc,dd)
        altered_output = proof_gen_function(a,b,c,d)
        # Calculate the Hamming distance
        distance = sum(o != a for o, a in zip(original_output, altered_output))
        differences.append(distance)
    return differences

def output_distribution_test(proof_gen_function, a,b, e ,challenges):
    outputs = [proof_gen_function(a,b,e,c) for c in challenges]
    flattened_outputs = [item for sublist in outputs for item in sublist]
    return Counter(flattened_outputs)


def generate_non_zero_vector(n,t):
    vector=list()
    while len(vector) != n:
        trial = secrets.randbelow(t)
        if trial != 0:
            vector.append(trial)
    return vector

def array_to_binary_string(coefficients):
    if len(coefficients) != 128:
        raise ValueError("Array must contain exactly 128 coefficients.")

    binary_string = ""
    for coeff in coefficients:
        if not (0 <= coeff < 512):
            raise ValueError("Each coefficient must be a 9-bit number (0 to 511 inclusive).")
        # Convert to binary, remove '0b' prefix, and pad with zeros to ensure 9 bits
        binary_repr = bin(coeff)[2:].zfill(8)
        binary_string += binary_repr

    return binary_string


def differential_analysis(function, input_sample, a, b, ca):
    differences = []
    for x in input_sample:
        # Choose a random index to modify
        idx = random.randint(0, len(x) - 1)
        
        # Create a modified input tuple
        modified_x = list(x)
        modified_x[idx] += 1  # Increment the selected element
        modified_x = tuple(modified_x)
        
        original_output = function(a, b, x)
        modified_output = function(a, b, modified_x)

        # Calculate the difference element-wise
        output_difference = [abs(o - m) for o, m in zip(original_output, modified_output)]
        differences.append(output_difference)
    return differences