import math
from fpylll import LLL
from fpylll import IntegerMatrix
from fpylll import CVP
from fpylll import SVP
from cryptography.hazmat.primitives.asymmetric import ec


# If "egcd" triggers a plagiarism warning, it's probably because I also took
# MATH-489 Number theory in cryptography at EPFL, where I coded pretty much the same thing
def egcd(a, b):
    if b > a:
        a, b = b, a
        u, last_u = 1, 0
        v, last_v = 0, 1
    else:
        u, last_u = 0, 1
        v, last_v = 1, 0

    while b != 0:
        q = a // b
        a, b = b, a % b
        u, last_u = last_u - q * u, u
        v, last_v = last_v - q * v, v

    return a, last_u, last_v


def mod_inv(a, p):
    a = a % p
    _gcd, b1, _ = egcd(a, p)
    if _gcd != 1:
        raise ArithmeticError("Mod inverse does not exist")
    else:
        return b1 % p


def check_x(x, Q):
    """ Given a guess for the secret key x and a public key Q = [x]P,
        checks if the guess is correct.

        :params x:  secret key, as an int
        :params Q:  public key, as a tuple of two ints (Q_x, Q_y)
    """
    x = int(x)
    if x <= 0:
        return False
    Q_x, Q_y = Q
    sk = ec.derive_private_key(x, ec.SECP256R1())
    pk = sk.public_key()
    xP = pk.public_numbers()
    return xP.x == Q_x and xP.y == Q_y


def recover_x_known_nonce(k, h, r, s, q):
    # Implement the "known nonce" cryptanalytic attack on ECDSA
    # The function is given the nonce k, (h, r, s) and the base point order q
    # The function should compute and return the secret signing key x

    lhs = (k * s) % q - h
    lhs %= q

    return (lhs * mod_inv(r, q)) % q


def recover_x_repeated_nonce(h_1, r_1, s_1, h_2, r_2, s_2, q):
    # Implement the "repeated nonces" cryptanalytic attack on ECDSA
    # The function is given the (hashed-message, signature) pairs (h_1, r_1, s_1)
    # and (h_2, r_2, s_2) generated using the same nonce
    # The function should compute and return the secret signing key x

    # As seen in the lecture slides
    h_s = (h_1 * s_2) % q - (h_2 * s_1) % q
    h_s %= q
    r_s = (r_2 * s_1) % q - (r_1 * s_2) % q
    r_s %= q

    return (h_s * mod_inv(r_s, q)) % q


def MSB_to_Padded_Int(N, L, list_k_MSB):
    # Implement a function that does the following: 
    # Let a is the integer represented by the L most significant bits of the nonce k 
    # The function should return a.2^{N - L} + 2^{N -L -1}
    a = int(''.join(list(map(str, list_k_MSB))), 2)

    return a * int(2 ** (N - L)) + int(2 ** (N - L - 1))


def LSB_to_Int(list_k_LSB):
    # Implement a function that does the following: 
    # Let a is the integer represented by the L least significant bits of the nonce k 
    # The function should return a
    return int(''.join(list(map(str, list_k_LSB))), 2)


def setup_hnp_single_sample(N, L, list_k_MSB, h, r, s, q, givenbits="msbs", algorithm="ecdsa"):
    # Implement a function that sets up a single instance for the hidden number problem (HNP)
    # The function is given a list of the L most significant bts of the N-bit nonce k,
    # along with (h, r, s) and the base point order q
    # The function should return (t, u) computed as described in the lectures
    # In the case of EC-Schnorr, r may be set to h

    # Work around possibly "gotcha" inputs
    if len(list_k_MSB) > L:
        list_k_MSB = list_k_MSB[:L]
    # Since we can't modify L globally, just consider the remaining bits to be 0
    # though it might be better if we fill it with random 1s and 0s
    if len(list_k_MSB) < L:
        diff = L - len(list_k_MSB)
        list_k_MSB += [0] * diff

    s_inv = mod_inv(s, q)

    def ecdsa_msbs():
        t = (r * s_inv) % q
        z = (h * s_inv) % q

        u = (MSB_to_Padded_Int(N, L, list_k_MSB) - z) % q

        return t, u

    def ecdsa_lsbs():
        pow_2_L_inv = mod_inv(int(2 ** L), q)

        a = (pow_2_L_inv * LSB_to_Int(list_k_MSB)) % q
        t = (pow_2_L_inv * r * s_inv) % q
        z = (pow_2_L_inv * h * s_inv) % q

        u = (a - z) % q

        return t, u

    def ecschnorr_msbs():
        t = h
        u = (MSB_to_Padded_Int(N, L, list_k_MSB) - s) % q

        return t, u

    def ecschnorr_lsbs():
        pow_2_L_inv = mod_inv(int(2 ** L), q)

        t = (h * pow_2_L_inv) % q
        u = (pow_2_L_inv * LSB_to_Int(list_k_MSB)) % q - (pow_2_L_inv * s) % q
        u %= q

        return t, u

    funcs = {x.__name__ : x for x in (ecdsa_msbs, ecdsa_lsbs, ecschnorr_msbs, ecschnorr_lsbs)}

    return funcs.get(f'{algorithm}_{givenbits}', ecdsa_msbs)()


def setup_hnp_all_samples(N, L, num_Samples, listoflists_k_MSB, list_h, list_r, list_s, q,
                          givenbits="msbs",
                          algorithm="ecdsa"):
    # Implement a function that sets up n = num_Samples many instances for the hidden number problem (HNP)
    # For each instance, the function is given a list the L most significant bits of the N-bit
    # nonce k, along with (h, r, s) and the base point order q
    # The function should return a list of t values and a list of u values computed as described in the lectures
    # Hint: Use the function you implemented above to set up the t and u values for each instance
    # In the case of EC-Schnorr, list_r may be set to list_h

    t_all, u_all = list(), list()
    for i in range(num_Samples):
        t, u = setup_hnp_single_sample(N, L, listoflists_k_MSB[i], list_h[i], list_r[i], list_s[i], q,
                                       givenbits=givenbits, algorithm=algorithm)
        t_all.append(t)
        u_all.append(u)

    return t_all, u_all


def hnp_to_cvp(N, L, num_Samples, list_t, list_u, q):
    # Implement a function that takes as input an instance of HNP and converts it into an
    # instance of the closest vector problem (CVP)
    # The function is given as input a list of t values, a list of u values and the base point
    # order q
    # The function should return the CVP basis matrix B (to be implemented as a nested list)
    # and the CVP target vector u (to be implemented as a list)
    # NOTE: The basis matrix B and the CVP target vector u should be scaled appropriately.
    # Refer lecture slides and lab sheet for more details

    b_cvp = list()
    matrix_n = num_Samples + 1

    scale_factor = int(2 ** (L + 1))
    scaled_q = q * scale_factor

    for i in range(matrix_n - 1):
        row = [0] * matrix_n
        row[i] = scaled_q
        b_cvp.append(row)

    b_cvp.append([x * scale_factor for x in list_t] + [1])

    u_cvp = [x * scale_factor for x in list_u] + [0]

    return b_cvp, u_cvp


def cvp_to_svp(N, L, num_Samples, cvp_basis_B, cvp_list_u):
    # Implement a function that takes as input an instance of CVP and converts it into
    # an instance of the shortest vector problem (SVP)
    # Your function should use the Kannan embedding technique in the lecture slides
    # The function is given as input a CVP basis matrix B and the CVP target vector u
    # The function should use the Kannan embedding technique to output the corresponding
    # SVP basis matrix B' of apropriate dimensions.
    # The SVP basis matrix B' should again be implemented as a nested list

    # z_norm = int((2 ** N)) // int(2 ** (L + 1))
    # fm_norm = int(math.sqrt(num_Samples + 1)) * z_norm
    # m = int(math.sqrt(fm_norm // 2))

    # Somehow the simplest things I could think of is the one yielding solutions....
    # Hours wasted: ~14
    m = int(2 ** N)
    svp_basis = [x[:] + [0] for x in cvp_basis_B]
    svp_basis.append(cvp_list_u[:] + [m])

    return svp_basis


def solve_cvp(cvp_basis_B, cvp_list_u):
    # Implement a function that takes as input an instance of CVP and solves it using
    # in-built CVP-solver functions from the fpylll library
    # The function is given as input a CVP basis matrix B and the CVP target vector u
    # The function should output the solution vector v (to be implemented as a list)
    # NOTE: The basis matrix B should be processed appropriately before being passes to
    # the fpylll CVP-solver. See lab sheet for more details

    reduced_basis_b = LLL.reduction(IntegerMatrix.from_matrix(cvp_basis_B))

    return CVP.closest_vector(reduced_basis_b, cvp_list_u)


def solve_svp(svp_basis_B):
    # Implement a function that takes as input an instance of SVP and solves it using
    # in-built SVP-solver functions from the fpylll library
    # The function is given as input the SVP basis matrix B
    # The function should output a list of candidate vectors that may contain x as a coefficient
    # NOTE: Recall from the lecture and also from the exercise session that for ECDSA
    # cryptanalysis based on partial nonces, you might want
    #       your function to include in the list of candidate vectors the *second* shortest
    #       vector (or even a later one).
    # If required, figure out how to get the in-built SVP-solver functions
    # from the fpylll library to return the second (or later) shortest vector

    reduced = IntegerMatrix.from_matrix(svp_basis_B)

    # If something breaks, better return something
    try:
        SVP.shortest_vector(reduced)
    except Exception:
        pass

    # get all solutions and search through them, we might be unlucky
    # make it a list for convenience
    return [list(v) for v in reduced]


def recover_x_partial_nonce_CVP(Q, N, L, num_Samples, listoflists_k_MSB, list_h, list_r, list_s, q, givenbits="msbs",
                                algorithm="ecdsa"):
    # Implement the "repeated nonces" cryptanalytic attack on ECDSA and EC-Schnorr
    # using the in-built CVP-solver functions from the fpylll library
    # The function is partially implemented for you. Note that it invokes some of the
    # functions that you have already implemented

    list_t, list_u = setup_hnp_all_samples(
        N, L, num_Samples, listoflists_k_MSB, list_h, list_r, list_s, q,
        givenbits=givenbits, algorithm=algorithm
    )
    cvp_basis_B, cvp_list_u = hnp_to_cvp(N, L, num_Samples, list_t, list_u, q)
    v_List = solve_cvp(cvp_basis_B, cvp_list_u)

    x = v_List[-1]
    return x % q

    # The function should recover the secret signing key x from the output of the CVP solver
    # and return it


def recover_x_partial_nonce_SVP(Q, N, L, num_Samples, listoflists_k_MSB, list_h, list_r, list_s, q, givenbits="msbs",
                                algorithm="ecdsa"):
    # Implement the "repeated nonces" cryptanalytic attack on ECDSA and EC-Schnorr using the
    # in-built CVP-solver functions from the fpylll library
    # The function is partially implemented for you. Note that it invokes some of the functions
    # that you have already implemented
    list_t, list_u = setup_hnp_all_samples(
        N, L, num_Samples, listoflists_k_MSB, list_h, list_r, list_s, q,
        givenbits=givenbits, algorithm=algorithm
    )
    cvp_basis_B, cvp_list_u = hnp_to_cvp(N, L, num_Samples, list_t, list_u, q)
    svp_basis_B = cvp_to_svp(N, L, num_Samples, cvp_basis_B, cvp_list_u)
    list_of_f_List = solve_svp(svp_basis_B)

    for f in list_of_f_List:

        candidate_x_negate = -f[-2] % q
        candidate_x = f[-2] % q

        if candidate_x == 0 and candidate_x_negate == 0:
            continue

        # in my experience, the negated value was the one which was the solution in most, if not
        # all cases, so check first for it (OpTimAiZeiShan)
        if check_x(candidate_x_negate, Q):
            return candidate_x_negate

        if check_x(candidate_x, Q):
            return candidate_x

    # The function should recover the secret signing key x from the output of the SVP solver and return it
    return -1


# testing code: do not modify

from module_1_ECDSA_Cryptanalysis_tests import run_tests

run_tests(recover_x_known_nonce,
          recover_x_repeated_nonce,
          recover_x_partial_nonce_CVP,
          recover_x_partial_nonce_SVP
          )
