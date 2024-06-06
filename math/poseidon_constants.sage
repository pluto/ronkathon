# Originally from: https://extgit.iaik.tugraz.at/krypto/hadeshash/-/blob/master/code/generate_params_poseidon.sage?ref_type=heads
# modified by: https://github.com/TaceoLabs/noir-poseidon/blob/main/scripts/poseidon_constants.sage

from math import *
import sys
from sage.rings.polynomial.polynomial_gf2x import GF2X_BuildIrred_list


# p = 2^251 + 17 * 2^192 + 1 = 0x800000000000011000000000000000000000000000000000000000000000001
# sage generate_params_poseidon.sage 1 0 252 3 3 128 0x800000000000011000000000000000000000000000000000000000000000001
# sage generate_params_poseidon.sage 1 0 252 4 3 128 0x800000000000011000000000000000000000000000000000000000000000001
# sage generate_params_poseidon.sage 1 0 252 8 3 128 0x800000000000011000000000000000000000000000000000000000000000001
# sage generate_params_poseidon.sage 1 0 252 16 3 128 0x800000000000011000000000000000000000000000000000000000000000001
###########################################################################

def get_alpha(p):
    for alpha in range(3, p):
        if gcd(alpha, p-1) == 1:
            break
    return alpha

def sat_inequiv_alpha(p, t, R_F, R_P, alpha, M):
    N = int(FIELD_SIZE * NUM_CELLS)

    if alpha > 0:
        R_F_1 = 6 if M <= ((floor(log(p, 2) - ((alpha-1)/2.0))) * (t + 1)) else 10 # Statistical
        R_F_2 = 1 + ceil(log(2, alpha) * min(M, FIELD_SIZE)) + ceil(log(t, alpha)) - R_P # Interpolation
        R_F_3 = (log(2, alpha) * min(M, log(p, 2))) - R_P # Groebner 1
        R_F_4 = t - 1 + log(2, alpha) * min(M / float(t + 1), log(p, 2) / float(2)) - R_P # Groebner 2
        R_F_5 = (t - 2 + (M / float(2 * log(alpha, 2))) - R_P) / float(t - 1) # Groebner 3
        R_F_max = max(ceil(R_F_1), ceil(R_F_2), ceil(R_F_3), ceil(R_F_4), ceil(R_F_5))

        # Addition due to https://eprint.iacr.org/2023/537.pdf
        r_temp = floor(t / 3.0)
        over = (R_F - 1) * t + R_P + r_temp + r_temp * (R_F / 2.0) + R_P + alpha
        under = r_temp * (R_F / 2.0) + R_P + alpha
        binom_log = log(binomial(over, under), 2)
        if binom_log == inf:
            binom_log = M + 1
        cost_gb4 = ceil(2 * binom_log) # Paper uses 2.3727, we are more conservative here

        return ((R_F >= R_F_max) and (cost_gb4 >= M))
    else:
        print("Invalid value for alpha!")
        exit(1)

def get_sbox_cost(R_F, R_P, N, t):
    return int(t * R_F + R_P)

def get_size_cost(R_F, R_P, N, t):
    n = ceil(float(N) / t)
    return int((N * R_F) + (n * R_P))

def get_depth_cost(R_F, R_P, N, t):
    return int(R_F + R_P)

def find_FD_round_numbers(p, t, alpha, M, cost_function, security_margin):
    N = int(FIELD_SIZE * NUM_CELLS)

    sat_inequiv = sat_inequiv_alpha

    R_P = 0
    R_F = 0
    min_cost = float("inf")
    max_cost_rf = 0
    # Brute-force approach
    for R_P_t in range(1, 500):
        for R_F_t in range(4, 100):
            if R_F_t % 2 == 0:
                if (sat_inequiv(p, t, R_F_t, R_P_t, alpha, M) == True):
                    if security_margin == True:
                        R_F_t += 2
                        R_P_t = int(ceil(float(R_P_t) * 1.075))
                    cost = cost_function(R_F_t, R_P_t, N, t)
                    if (cost < min_cost) or ((cost == min_cost) and (R_F_t < max_cost_rf)):
                        R_P = ceil(R_P_t)
                        R_F = ceil(R_F_t)
                        min_cost = cost
                        max_cost_rf = R_F
    return (int(R_F), int(R_P))

def calc_final_numbers_fixed(p, t, alpha, M, security_margin):
    # [Min. S-boxes] Find best possible for t and N
    N = int(FIELD_SIZE * NUM_CELLS)
    cost_function = get_sbox_cost
    ret_list = []
    (R_F, R_P) = find_FD_round_numbers(p, t, alpha, M, cost_function, security_margin)
    min_sbox_cost = cost_function(R_F, R_P, N, t)
    ret_list.append(R_F)
    ret_list.append(R_P)
    ret_list.append(min_sbox_cost)

    # [Min. Size] Find best possible for t and N
    # Minimum number of S-boxes for fixed n results in minimum size also (round numbers are the same)!
    min_size_cost = get_size_cost(R_F, R_P, N, t)
    ret_list.append(min_size_cost)

    return ret_list # [R_F, R_P, min_sbox_cost, min_size_cost]

def print_latex_table_combinations(combinations, alpha, security_margin):
    for comb in combinations:
        N = comb[0]
        t = comb[1]
        M = comb[2]
        n = int(N / t)
        prime = PRIME_NUMBER
        ret = calc_final_numbers_fixed(prime, t, alpha, M, security_margin)
        field_string = "\mathbb F_{p}"
        sbox_string = "x^{" + str(alpha) + "}"
        print("$" + str(M) + "$ & $" + str(N) + "$ & $" + str(n) + "$ & $" + str(t) + "$ & $" + str(ret[0]) + "$ & $" + str(ret[1]) + "$ & $" + field_string + "$ & $" + str(ret[2]) + "$ & $" + str(ret[3]) + "$ \\\\")


###
### Matrices and round constants
###
def grain_sr_generator():
    bit_sequence = INIT_SEQUENCE
    for _ in range(0, 160):
        new_bit = bit_sequence[62] ^^ bit_sequence[51] ^^ bit_sequence[38] ^^ bit_sequence[23] ^^ bit_sequence[13] ^^ bit_sequence[0]
        bit_sequence.pop(0)
        bit_sequence.append(new_bit)

    while True:
        new_bit = bit_sequence[62] ^^ bit_sequence[51] ^^ bit_sequence[38] ^^ bit_sequence[23] ^^ bit_sequence[13] ^^ bit_sequence[0]
        bit_sequence.pop(0)
        bit_sequence.append(new_bit)
        while new_bit == 0:
            new_bit = bit_sequence[62] ^^ bit_sequence[51] ^^ bit_sequence[38] ^^ bit_sequence[23] ^^ bit_sequence[13] ^^ bit_sequence[0]
            bit_sequence.pop(0)
            bit_sequence.append(new_bit)
            new_bit = bit_sequence[62] ^^ bit_sequence[51] ^^ bit_sequence[38] ^^ bit_sequence[23] ^^ bit_sequence[13] ^^ bit_sequence[0]
            bit_sequence.pop(0)
            bit_sequence.append(new_bit)
        new_bit = bit_sequence[62] ^^ bit_sequence[51] ^^ bit_sequence[38] ^^ bit_sequence[23] ^^ bit_sequence[13] ^^ bit_sequence[0]
        bit_sequence.pop(0)
        bit_sequence.append(new_bit)
        yield new_bit

def grain_random_bits(num_bits):
    random_bits = [next(grain_gen) for i in range(0, num_bits)]
    # random_bits.reverse() ## Remove comment to start from least significant bit
    random_int = int("".join(str(i) for i in random_bits), 2)
    return random_int

def init_generator(field, sbox, n, t, R_F, R_P):
    # Generate initial sequence based on parameters
    bit_list_field = [_ for _ in (bin(FIELD)[2:].zfill(2))]
    bit_list_sbox = [_ for _ in (bin(SBOX)[2:].zfill(4))]
    bit_list_n = [_ for _ in (bin(FIELD_SIZE)[2:].zfill(12))]
    bit_list_t = [_ for _ in (bin(NUM_CELLS)[2:].zfill(12))]
    bit_list_R_F = [_ for _ in (bin(R_F)[2:].zfill(10))]
    bit_list_R_P = [_ for _ in (bin(R_P)[2:].zfill(10))]
    bit_list_1 = [1] * 30
    global INIT_SEQUENCE
    INIT_SEQUENCE = bit_list_field + bit_list_sbox + bit_list_n + bit_list_t + bit_list_R_F + bit_list_R_P + bit_list_1
    INIT_SEQUENCE = [int(_) for _ in INIT_SEQUENCE]

def generate_constants(field, n, t, R_F, R_P, prime_number):
    round_constants = []
    num_constants = (R_F + R_P) * t

    if field == 0:
        for i in range(0, num_constants):
            random_int = grain_random_bits(n)
            round_constants.append(random_int)
    elif field == 1:
        for i in range(0, num_constants):
            random_int = grain_random_bits(n)
            while random_int >= prime_number:
                # print("[Info] Round constant is not in prime field! Taking next one.")
                random_int = grain_random_bits(n)
            round_constants.append(random_int)
    return round_constants

def print_round_constants(round_constants, n, field, FILE):
    #print("Number of round constants:", len(round_constants))
    if write_file == True:
        FILE.write("Number of round constants: " + str(len(round_constants)) + "\n")

    if field == 0:
        print("Round constants for GF(2^n):")
        if write_file == True:
            FILE.write("Round constants for GF(2^n):\n")
    elif field == 1:
        #print("Round constants for GF(p):")
        if write_file == True:
            FILE.write("Round constants for GF(p):\n")
    hex_length = int(ceil(float(n) / 4)) + 2 # +2 for "0x"
    print(["{0:#0{1}x}".format(entry, hex_length) for entry in round_constants])
    if write_file == True:
        FILE.write(str(["{0:#0{1}x}".format(entry, hex_length) for entry in round_constants]) + "\n")

def create_mds_p(n, t):
    M = matrix(F, t, t)

    # Sample random distinct indices and assign to xs and ys
    while True:
        flag = True
        rand_list = [F(grain_random_bits(n)) for _ in range(0, 2*t)]
        while len(rand_list) != len(set(rand_list)): # Check for duplicates
            rand_list = [F(grain_random_bits(n)) for _ in range(0, 2*t)]
        xs = rand_list[:t]
        ys = rand_list[t:]
        # xs = [F(ele) for ele in range(0, t)]
        # ys = [F(ele) for ele in range(t, 2*t)]
        for i in range(0, t):
            for j in range(0, t):
                if (flag == False) or ((xs[i] + ys[j]) == 0):
                    flag = False
                else:
                    entry = (xs[i] + ys[j])^(-1)
                    M[i, j] = entry
        if flag == False:
            continue
        return M

def create_mds_gf2n(n, t):
    M = matrix(F, t, t)

    # Sample random distinct indices and assign to xs and ys
    while True:
        flag = True
        rand_list = [F.fetch_int(grain_random_bits(n)) for _ in range(0, 2*t)]
        while len(rand_list) != len(set(rand_list)): # Check for duplicates
            rand_list = [F.fetch_int(grain_random_bits(n)) for _ in range(0, 2*t)]
        xs = rand_list[:t]
        ys = rand_list[t:]
        for i in range(0, t):
            for j in range(0, t):
                if (flag == False) or ((xs[i] + ys[j]) == 0):
                    flag = False
                else:
                    entry = (xs[i] + ys[j])^(-1)
                    M[i, j] = entry
        if flag == False:
            continue
        return M

def generate_vectorspace(round_num, M, M_round, NUM_CELLS):
    t = NUM_CELLS
    s = 1
    V = VectorSpace(F, t)
    if round_num == 0:
        return V
    elif round_num == 1:
        return V.subspace(V.basis()[s:])
    else:
        mat_temp = matrix(F)
        for i in range(0, round_num-1):
            add_rows = []
            for j in range(0, s):
                add_rows.append(M_round[i].rows()[j][s:])
            mat_temp = matrix(mat_temp.rows() + add_rows)
        r_k = mat_temp.right_kernel()
        extended_basis_vectors = []
        for vec in r_k.basis():
            extended_basis_vectors.append(vector([0]*s + list(vec)))
        S = V.subspace(extended_basis_vectors)

        return S

def subspace_times_matrix(subspace, M, NUM_CELLS):
    t = NUM_CELLS
    V = VectorSpace(F, t)
    subspace_basis = subspace.basis()
    new_basis = []
    for vec in subspace_basis:
        new_basis.append(M * vec)
    new_subspace = V.subspace(new_basis)
    return new_subspace

# Returns True if the matrix is considered secure, False otherwise
def algorithm_1(M, NUM_CELLS):
    t = NUM_CELLS
    s = 1
    r = floor((t - s) / float(s))

    # Generate round matrices
    M_round = []
    for j in range(0, t+1):
        M_round.append(M^(j+1))

    for i in range(1, r+1):
        mat_test = M^i
        entry = mat_test[0, 0]
        mat_target = matrix.circulant(vector([entry] + ([F(0)] * (t-1))))

        if (mat_test - mat_target) == matrix.circulant(vector([F(0)] * (t))):
            return [False, 1]

        S = generate_vectorspace(i, M, M_round, t)
        V = VectorSpace(F, t)

        basis_vectors= []
        for eigenspace in mat_test.eigenspaces_right(format='galois'):
            if (eigenspace[0] not in F):
                continue
            vector_subspace = eigenspace[1]
            intersection = S.intersection(vector_subspace)
            basis_vectors += intersection.basis()
        IS = V.subspace(basis_vectors)

        if IS.dimension() >= 1 and IS != V:
            return [False, 2]
        for j in range(1, i+1):
            S_mat_mul = subspace_times_matrix(S, M^j, t)
            if S == S_mat_mul:
                print("S.basis():\n", S.basis())
                return [False, 3]

    return [True, 0]

# Returns True if the matrix is considered secure, False otherwise
def algorithm_2(M, NUM_CELLS):
    t = NUM_CELLS
    s = 1

    V = VectorSpace(F, t)
    trail = [None, None]
    test_next = False
    I = range(0, s)
    I_powerset = list(sage.misc.misc.powerset(I))[1:]
    for I_s in I_powerset:
        test_next = False
        new_basis = []
        for l in I_s:
            new_basis.append(V.basis()[l])
        IS = V.subspace(new_basis)
        for i in range(s, t):
            new_basis.append(V.basis()[i])
        full_iota_space = V.subspace(new_basis)
        for l in I_s:
            v = V.basis()[l]
            while True:
                delta = IS.dimension()
                v = M * v
                IS = V.subspace(IS.basis() + [v])
                if IS.dimension() == t or IS.intersection(full_iota_space) != IS:
                    test_next = True
                    break
                if IS.dimension() <= delta:
                    break
            if test_next == True:
                break
        if test_next == True:
            continue
        return [False, [IS, I_s]]

    return [True, None]

# Returns True if the matrix is considered secure, False otherwise
def algorithm_3(M, NUM_CELLS):
    t = NUM_CELLS
    s = 1

    V = VectorSpace(F, t)

    l = 4*t
    for r in range(2, l+1):
        next_r = False
        res_alg_2 = algorithm_2(M^r, t)
        if res_alg_2[0] == False:
            return [False, None]

        # if res_alg_2[1] == None:
        #     continue
        # IS = res_alg_2[1][0]
        # I_s = res_alg_2[1][1]
        # for j in range(1, r):
        #     IS = subspace_times_matrix(IS, M, t)
        #     I_j = []
        #     for i in range(0, s):
        #         new_basis = []
        #         for k in range(0, t):
        #             if k != i:
        #                 new_basis.append(V.basis()[k])
        #         iota_space = V.subspace(new_basis)
        #         if IS.intersection(iota_space) != iota_space:
        #             single_iota_space = V.subspace([V.basis()[i]])
        #             if IS.intersection(single_iota_space) == single_iota_space:
        #                 I_j.append(i)
        #             else:
        #                 next_r = True
        #                 break
        #     if next_r == True:
        #         break
        # if next_r == True:
        #     continue
        # return [False, [IS, I_j, r]]

    return [True, None]

def generate_matrix(FIELD, FIELD_SIZE, NUM_CELLS):
    if FIELD == 0:
        mds_matrix = create_mds_gf2n(FIELD_SIZE, NUM_CELLS)
        result_1 = algorithm_1(mds_matrix, NUM_CELLS)
        result_2 = algorithm_2(mds_matrix, NUM_CELLS)
        result_3 = algorithm_3(mds_matrix, NUM_CELLS)
        while result_1[0] == False or result_2[0] == False or result_3[0] == False:
            mds_matrix = create_mds_p(FIELD_SIZE, NUM_CELLS)
            result_1 = algorithm_1(mds_matrix, NUM_CELLS)
            result_2 = algorithm_2(mds_matrix, NUM_CELLS)
            result_3 = algorithm_3(mds_matrix, NUM_CELLS)
        return mds_matrix
    elif FIELD == 1:
        mds_matrix = create_mds_p(FIELD_SIZE, NUM_CELLS)
        result_1 = algorithm_1(mds_matrix, NUM_CELLS)
        result_2 = algorithm_2(mds_matrix, NUM_CELLS)
        result_3 = algorithm_3(mds_matrix, NUM_CELLS)
        while result_1[0] == False or result_2[0] == False or result_3[0] == False:
            mds_matrix = create_mds_p(FIELD_SIZE, NUM_CELLS)
            result_1 = algorithm_1(mds_matrix, NUM_CELLS)
            result_2 = algorithm_2(mds_matrix, NUM_CELLS)
            result_3 = algorithm_3(mds_matrix, NUM_CELLS)
        return mds_matrix

def print_linear_layer(M, n, t):
    print("n:", n)
    print("t:", t)
    print("N:", (n * t))
    print("Result Algorithm 1:\n", algorithm_1(M, NUM_CELLS))
    print("Result Algorithm 2:\n", algorithm_2(M, NUM_CELLS))
    print("Result Algorithm 3:\n", algorithm_3(M, NUM_CELLS))
    if write_file == True:
        FILE.write("n: " + str(n) + "\n")
        FILE.write("t: " + str(t) + "\n")
        FILE.write("N: " + str(n * t) + "\n")
        FILE.write("Result Algorithm 1:\n" + str(algorithm_1(M, NUM_CELLS)) + "\n")
        FILE.write("Result Algorithm 2:\n" + str(algorithm_2(M, NUM_CELLS)) + "\n")
        FILE.write("Result Algorithm 3:\n" + str(algorithm_3(M, NUM_CELLS)) + "\n")

    hex_length = int(ceil(float(n) / 4)) + 2 # +2 for "0x"
    if FIELD == 0:
        print("Modulus:", PRIME_NUMBER)
        if write_file == True:
            FILE.write("Modulus: " + str(PRIME_NUMBER) + "\n")
    elif FIELD == 1:
        print("Prime number:", hex(PRIME_NUMBER))
        if write_file == True:
            FILE.write("Prime number: " + hex(PRIME_NUMBER) + "\n")
    matrix_string = "["
    for i in range(0, t):
        if FIELD == 0:
            matrix_string += str(["{0:#0{1}x}".format(entry.integer_representation(), hex_length) for entry in M[i]])
        elif FIELD == 1:
            matrix_string += str(["{0:#0{1}x}".format(int(entry), hex_length) for entry in M[i]])
        if i < (t-1):
            matrix_string += ","
    matrix_string += "]"
    print("MDS matrix:\n", matrix_string)
    if write_file == True:
        FILE.write("MDS matrix:\n" + str(matrix_string))

def print_rust(state_size, rc, mds, f, alpha, num_f, num_p):
  assert(len(rc) % state_size == 0)
  assert(mds.nrows() == state_size)
  assert(mds.ncols() == state_size)
  f.write("pub const ALPHA: usize = {};\n".format(int(alpha)))
  f.write("pub const WIDTH: usize = {};\n".format(int(state_size)))
  f.write("pub const NUM_F: usize = {};\n".format(int(num_f)))
  f.write("pub const NUM_P: usize = {};\n".format(int(num_p)))
  f.write("pub fn constants() -> (Vec<usize>, Vec<Vec<usize>>) {\n")
  f.write("let RC{}: Vec<usize> = vec![\n".format(state_size))
  for e in rc:
        #   f.write("from_hex(\"{0:#0{1}x}\").unwrap(), ".format(e,int(66)))
    f.write("{},".format(int(e)))
  f.write("];")

  f.write("\n\n")

  f.write("let MDS{}: Vec<Vec<usize>> = vec![".format(state_size))
  for i in range(0, mds.nrows()):
      f.write("vec![")
      for j in range(0, mds.ncols()):
        #   f.write("from_hex(\"{0:#0{1}x}\").unwrap(), ".format(int(mds[i][j]), int(66)))
        f.write("{}, ".format(int(mds[i][j])))
      f.write("],\n")
  f.write("];\n")
  f.write("(RC{},MDS{})".format(state_size, state_size))
  f.write("}\n")
  f.write("\n\n")
#   f.write("pub static ref POSEIDON_{}_PARAMS: PoseidonConfig<F> =".format(state_size))
#   f.write("Arc::new(PoseidonParams::new({0}, 5, 8, {1}, &MDS{0}, &RC{0}));".format(state_size, steps - 8))

# p = 2^251 + 17 * 2^192 + 1 = 0x800000000000011000000000000000000000000000000000000000000000001
# sage generate_params_poseidon.sage 1 0 252 3 3 128 0x800000000000011000000000000000000000000000000000000000000000001
# sage generate_params_poseidon.sage 1 0 252 4 3 128 0x800000000000011000000000000000000000000000000000000000000000001
# sage generate_params_poseidon.sage 1 0 252 8 3 128 0x800000000000011000000000000000000000000000000000000000000000001
# sage generate_params_poseidon.sage 1 0 252 16 3 128 0x800000000000011000000000000000000000000000000000000000000000001
if len(sys.argv) < 8:
    print("Usage: <script> <field> <s_box> <field_size> <num_cells> <alpha> <security_level> <modulus_hex>")
    print("field = 1 for GF(p)")
    print("s_box = 0 for x^alpha, s_box = 1 for x^(-1)")
    exit()

# Flags
write_file = False

# Parameters
FIELD = int(sys.argv[1]) # 0 .. GF(2^n), 1 .. GF(p)
SBOX = int(sys.argv[2]) # 0 .. x^alpha, 1 .. x^(-1)
FIELD_SIZE = int(sys.argv[3]) # n
NUM_CELLS = int(sys.argv[4]) # t
ALPHA = int(sys.argv[5])
SECURITY_LEVEL = int(sys.argv[6])
R_F_FIXED = 0
R_P_FIXED = 0

INIT_SEQUENCE = []

PRIME_NUMBER = 0
F = None
if FIELD == 0:
    #PRIME_NUMBER = GF(2)['x'](GF2X_BuildIrred_list(FIELD_SIZE))
    PRIME_NUMBER = int(sys.argv[7], 16)
    F.<x> = GF(2**FIELD_SIZE, name='x', modulus = PRIME_NUMBER)
elif FIELD == 1:
    PRIME_NUMBER = int(sys.argv[7], 16)
    F = GF(PRIME_NUMBER)
else:
    print("Unknown field type, only 0 and 1 supported!")
    exit()

t = NUM_CELLS
###
### Get round number first
###
ROUND_NUMBERS = calc_final_numbers_fixed(PRIME_NUMBER, NUM_CELLS, ALPHA, SECURITY_LEVEL, True)
R_F_FIXED = ROUND_NUMBERS[0]
R_P_FIXED = ROUND_NUMBERS[1]
# R_F_FIXED = 8
# R_P_FIXED = 60
alpha = get_alpha(PRIME_NUMBER)
assert(alpha == ALPHA, "alpha doesn't match")

print("Params: n=%d, t=%d, alpha=%d, M=%d, R_F=%d, R_P=%d"%(FIELD_SIZE, NUM_CELLS, ALPHA, SECURITY_LEVEL, R_F_FIXED, R_P_FIXED))
print("Modulus = %d"%(PRIME_NUMBER))
print("Number of S-boxes:", ROUND_NUMBERS[2])
# print("Number of S-boxes per state element:", ceil(ROUND_NUMBERS[2] / float(NUM_CELLS)))
grain_gen = grain_sr_generator()

FILE = None
if write_file == True:
  FILE = open("poseidon_params_n%d_t%d_alpha%d_M%d.txt"%(FIELD_SIZE, NUM_CELLS, ALPHA, SECURITY_LEVEL),'w')
  FILE.write("Params: n=%d, t=%d, alpha=%d, M=%d, R_F=%d, R_P=%d\n"%(FIELD_SIZE, NUM_CELLS, ALPHA, SECURITY_LEVEL, R_F_FIXED, R_P_FIXED))
  FILE.write("Modulus = %d\n"%(PRIME_NUMBER))
  FILE.write("Number of S-boxes: %d\n"%(ROUND_NUMBERS[2]))
  FILE.write("Number of S-boxes per state element: %d\n"%(ceil(ROUND_NUMBERS[2] / float(NUM_CELLS))))
with open('rc_poseidon_{}'.format(t), 'w') as f:
    # Init
    init_generator(FIELD, SBOX, FIELD_SIZE, NUM_CELLS, R_F_FIXED, R_P_FIXED)
    # Round constants
    round_constants = generate_constants(FIELD, FIELD_SIZE, NUM_CELLS, R_F_FIXED, R_P_FIXED, PRIME_NUMBER)
	# Matrix
    MDS = generate_matrix(FIELD, FIELD_SIZE, NUM_CELLS)
    print_rust(t, round_constants, MDS, f, ALPHA, R_F_FIXED, R_P_FIXED)
    print("done with {}".format(t))

if write_file == True:
    FILE.close()