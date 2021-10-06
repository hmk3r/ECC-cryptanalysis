from module_1_ECDSA_Cryptanalysis_Skel import setup_hnp_single_sample

q = 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
N = 256
L = 128

MSBs = list()
h = list()
r = list()
s = list()
t = list()
u = list()

with open('testvectors_hnp_single_sample_256_128_reformat.txt') as f:
    while True:
        line = f.readline()
        if not line:
            break
        MSBs.append(list(map(int, line.split())))
        h.append(int(f.readline()))
        r.append(int(f.readline()))
        s.append(int(f.readline()))
        t.append(int(f.readline()))
        u.append(int(f.readline()))

res = list()

for i, MSB in enumerate(MSBs):
    t_res, u_res = setup_hnp_single_sample(N, L, MSB, h[i], r[i], s[i], q)
    res.append(True if t_res == t[i] and u_res == u[i] else False)

print('All Good!' if all(res) else 'Cucked')
