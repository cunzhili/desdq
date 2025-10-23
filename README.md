from charm.toolbox.integergroup import IntegerGroup
from charm.schemes.pkenc.pkenc_rsa import RSA_Enc, RSA_Sig
from charm.core.math.integer import integer, randomBits, random, randomPrime, isPrime, encode, decode, hashInt, bitsize, \
    legendre, gcd, lcm, serialize, deserialize, int2Bytes, toInt
import hashlib
import struct
import time
import random as py_random
import sys
import heapq


class DTPKC():
    def __init__(self, secparam=1024):
        self.p, self.q = randomPrime(secparam, True), randomPrime(secparam, True)
        self.pp = (self.p - 1) / 2
        self.qq = (self.q - 1) / 2
        self.N = self.p * self.q
        self.N2 = self.N ** 2
        self.lamda = lcm(self.p - 1, self.q - 1) / 2

        self.a = random(self.N2)
        tmp = self.a ** (2 * self.N)
        self.g = (int(self.N2) - int(tmp)) % self.N2
        self.mk = self.lamda

    def GetMK(self):
        return self.mk

    def KeyGen(self):
        theta = random(self.N / 4)
        h = self.g ** (theta) % self.N2
        pk = {"N": self.N, "g": self.g, "h": h}
        sk = theta
        return pk, sk

    def Encrypt(self, pk, plaintext):
        r = random(self.N / 4)
        T1 = int(pk["h"] ** (r)) * int(1 + plaintext * self.N) % self.N2
        T2 = pk["g"] ** (r) % self.N2
        ciphertext = {"T1": T1, "T2": T2}
        return ciphertext

    def Decrypt(self, ciphertext, sk):
        T1 = ciphertext["T1"]
        T2 = ciphertext["T2"]
        tmp = (T1 / (T2 ** sk)) % self.N2
        m = (int(tmp) - 1) / self.N
        return m

    def DecryptMK(self, ciphertext, mk):
        tmp = ciphertext["T1"] ** (mk) % self.N2
        mk = mk % self.N
        mk_1 = mk ** (-1)

        m = ((int(tmp) - 1) / self.N) * int(mk_1) % self.N
        return integer(m)

    def SplitMK(self, mk):
        mk = mk % self.N
        mk_1 = mk ** (-1)
        tmp = int(mk) * int(int(mk_1) % self.N2)
        modulus = int(mk) * int(self.N2)
        s = tmp % modulus
        lamda1 = random(s)
        lamda2 = s - int(lamda1)
        return integer(lamda1), integer(lamda2)

    def PSDec1(self, ciphertext, lamda1):
        ct1 = ciphertext["T1"] ** (lamda1)
        return ct1

    def PSDec2(self, ciphertext, lamda2, ct1):
        ct2 = ciphertext["T1"] ** (lamda2)
        T = ct1 * ct2
        T_int = int(T)
        N_int = int(self.N)
        m = (T_int - 1) // N_int
        return integer(int(m))


def SAP(cipher1, cipher2, pk):
    N = pk["N"]
    N2 = N * N  # 用N计算N2，而非从pk中获取
    T1 = (cipher1["T1"] * cipher2["T1"]) % N2
    T2 = (cipher1["T2"] * cipher2["T2"]) % N2
    return {"T1": T1, "T2": T2}


class SCP:
    """优化后的安全比较协议"""

    def __init__(self, dtpkc):
        self.dtpkc = dtpkc
        self.csp1_pk, self.csp1_sk = dtpkc.KeyGen()
        self.csp2_pk, self.csp2_sk = dtpkc.KeyGen()

        # 预计算常用值
        self.N = self.csp1_pk["N"]
        self.N2 = self.N * self.N
        self.N_minus_1 = self.N - 1

    def compare(self, cipher1, cipher2):
        """修正的安全比较协议"""
        # 预计算平方值
        c1_T1_sq = (cipher1["T1"] ** 2) % self.N2
        c1_T2_sq = (cipher1["T2"] ** 2) % self.N2
        c2_T1_sq = (cipher2["T1"] ** 2) % self.N2
        c2_T2_sq = (cipher2["T2"] ** 2) % self.N2

        # 密文变换
        c1_tilde = {
            "T1": (c1_T1_sq * (self.csp1_pk["h"] ** 1 % self.N2)) % self.N2,
            "T2": c1_T2_sq
        }
        c2_tilde = {
            "T1": c2_T1_sq,
            "T2": c2_T2_sq
        }

        # 生成随机位b
        b = random(2)

        # 根据b值计算比较结果密文
        if b == 1:
            c2_neg = {
                "T1": (c2_tilde["T1"] ** self.N_minus_1) % self.N2,
                "T2": (c2_tilde["T2"] ** self.N_minus_1) % self.N2
            }
            res_cipher = SAP(c1_tilde, c2_neg, self.csp1_pk)
        else:
            c1_neg = {
                "T1": (c1_tilde["T1"] ** self.N_minus_1) % self.N2,
                "T2": (c1_tilde["T2"] ** self.N_minus_1) % self.N2
            }
            res_cipher = SAP(c1_neg, c2_tilde, self.csp1_pk)

        # 混淆结果 - 修正：对整个密文进行混淆
        r = random(self.N / 4)
        res_cipher_confused = {
            "T1": (res_cipher["T1"] ** r) % self.N2,
            "T2": (res_cipher["T2"] ** r) % self.N2
        }

        # 协同解密 - 修正：使用混淆后的密文
        lamda1, lamda2 = self.dtpkc.SplitMK(self.dtpkc.mk)
        RES1 = self.dtpkc.PSDec1(res_cipher_confused, lamda1)
        RES2 = self.dtpkc.PSDec2(res_cipher_confused, lamda2, RES1)

        # 判断结果
        L_N = bitsize(self.N)
        L_RES2 = bitsize(RES2)
        flag = 1 if L_RES2 > (L_N / 2) else 0

        final_result = flag == 1 if b == 0 else flag == 1
        return final_result


class PRF:
    """伪随机函数"""

    def __init__(self, key):
        self.key = hashlib.sha256(str(key).encode()).digest()

    def evaluate(self, x):
        x_bytes = str(x).encode()
        hmac = hashlib.pbkdf2_hmac('sha256', x_bytes, self.key, 10)
        return int.from_bytes(hmac[:8], 'big')


class RandomOracle:
    """随机预言机"""

    @staticmethod
    def H(data):
        if isinstance(data, tuple):
            data_str = '|'.join(str(x) for x in data)
        else:
            data_str = str(data)
        h = hashlib.sha256(data_str.encode()).digest()
        return int.from_bytes(h[:16], 'big')


class GESDQ:
    """GESDQ图加密方案 - 严格按照算法1和算法2实现"""

    def __init__(self, secparam=512):
        print("初始化GESDQ系统...")
        self.secparam = secparam
        self.dtpkc = DTPKC(secparam)
        self.scp = SCP(self.dtpkc)
        self.pk = self.dtpkc.pk

        self.DX = {}
        self.Arr = {}
        self.pi = None

        print("GESDQ系统初始化完成")

    def encrypt_graph(self, graph):
        """图加密算法 - 严格按照算法1实现"""
        print("开始加密图...")
        V = list(graph.keys())
        N = len(V)

        # 计算总边数
        M = 0
        for u in V:
            M += len(graph[u])

        print(f"图规模: {N}个顶点, {M}条边")

        # 初始化数据结构
        self.DX = {}
        self.Arr = {}
        self.pi = self._generate_permutation(M)

        # 生成密钥
        self.k1 = randomBits(128)
        self.k2 = randomBits(128)

        prf_k1 = PRF(self.k1)
        prf_k2 = PRF(self.k2)

        ctr = 1

        # 处理每个顶点
        for i, u in enumerate(V):
            if i % 100 == 0:
                print(f"加密进度: {i}/{N} 个顶点")

            # 为每个顶点生成密钥K_u
            K_u = randomBits(128)
            neighbors = list(graph[u].items())

            # 处理每个邻居
            for j, (v, dis_uv) in enumerate(neighbors):
                # 加密距离
                c_i = self.dtpkc.Encrypt(self.pk, integer(dis_uv))

                # 构建邻居信息N_i
                if j < len(neighbors) - 1:
                    # 不是最后一个邻居，有下一个指针
                    N_i = (prf_k1.evaluate(v), prf_k2.evaluate(v), c_i, self.pi.apply(ctr + 1))
                else:
                    # 最后一个邻居，下一个指针为None
                    N_i = (prf_k1.evaluate(v), prf_k2.evaluate(v), c_i, None)

                # 生成随机数r_i
                r_i = randomBits(128)

                # 使用H(K_u || r_i)加密N_i
                H_value = RandomOracle.H((str(K_u), str(r_i)))
                encrypted_N_i = tuple(
                    x ^ H_value if isinstance(x, int) else x
                    for x in N_i
                )

                # 存储到Arr中
                self.Arr[self.pi.apply(ctr)] = (encrypted_N_i, r_i)
                ctr += 1

            # 设置DX条目 - 严格按照算法1第17行
            if neighbors:
                add_N1 = self.pi.apply(ctr - len(neighbors))  # 第一个邻居的地址
                DX_value = (add_N1, K_u)
                # 使用F_k2(u)加密DX值
                u_hash = prf_k2.evaluate(u)
                encrypted_DX = tuple(
                    x ^ u_hash if isinstance(x, int) else x
                    for x in DX_value
                )
                self.DX[prf_k1.evaluate(u)] = encrypted_DX

        encrypted_graph = {
            "DX": self.DX,
            "Arr": self.Arr,
            "pi": self.pi,
            "k1": self.k1,
            "k2": self.k2
        }

        storage_MB = self._calculate_storage_cost(encrypted_graph)
        encrypted_graph["storage_cost_MB"] = storage_MB

        print(f"图加密完成: {N}个顶点, {M}条边, 存储成本: {storage_MB:.2f} MB")
        return encrypted_graph

    def shortest_distance_query(self, u, v, encrypted_graph):
        """最短距离查询 - 严格按照算法2实现"""
        print(f"执行查询: {u} -> {v}")

        DX = encrypted_graph["DX"]
        Arr = encrypted_graph["Arr"]
        k1 = encrypted_graph["k1"]
        k2 = encrypted_graph["k2"]

        prf_k1 = PRF(k1)
        prf_k2 = PRF(k2)

        # 步骤1: 计算令牌
        tk1 = prf_k1.evaluate(u)  # tk1 = F_k1(u)
        tk2 = prf_k2.evaluate(u)  # tk2 = F_k2(u)
        tk3 = prf_k1.evaluate(v)  # tk3 = F_k1(v)

        print(f"令牌: tk1={tk1}, tk2={tk2}, tk3={tk3}")

        # 步骤3: 查找起点和终点
        alpha_u = DX.get(tk1)
        alpha_v = DX.get(tk3)

        # 步骤4-6: 检查是否存在
        if alpha_u is None:
            print(f"错误: 未找到起点 {u} 在DX中")
            return None
        if alpha_v is None:
            print(f"错误: 未找到终点 {v} 在DX中")
            return None

        print("找到起点和终点在DX中")

        # 步骤7: 初始化集合
        Pass = set()  # 已处理节点集合
        UPass = []  # 未处理节点集合，存储(a_i, b_i, c_i)三元组

        # 步骤8: 将起点加入Pass
        start_node = (prf_k1.evaluate(u), prf_k2.evaluate(u))
        Pass.add(start_node)

        # 步骤9-18: 处理起点的邻居
        add_start_encrypted, K_u_encrypted = alpha_u
        # 步骤9: 解密DX值
        add_start = add_start_encrypted ^ tk2
        K_u = K_u_encrypted ^ tk2

        current_add = add_start
        i = 1

        # 步骤12-18: 遍历邻居链表
        while current_add is not None:
            if current_add not in Arr:
                break

            # 步骤10, 13, 15: 获取并解密邻居信息
            beta_i, r_i = Arr[current_add]
            H_value = RandomOracle.H((str(K_u), str(r_i)))
            N_i = tuple(
                x ^ H_value if isinstance(x, int) else x
                for x in beta_i
            )

            a_i, b_i, c_i, next_add = N_i

            # 步骤14: 将邻居加入UPass
            UPass.append((a_i, b_i, c_i))

            current_add = next_add
            i += 1

        print(f"初始UPass大小: {len(UPass)}")

        # 步骤19-44: 主循环
        iteration = 0
        while UPass and iteration < 1000:
            iteration += 1

            # 步骤20: 对UPass按距离排序（使用SCP协议）
            # 这里简化实现，实际应该使用SCP协议进行安全比较
            UPass_sorted = self._sort_upass_by_distance(UPass)

            # 步骤21: 选择距离最小的节点
            if not UPass_sorted:
                break

            a_j, b_j, c_j = UPass_sorted[0]
            UPass = UPass_sorted[1:]  # 从UPass中删除

            current_node = (a_j, b_j)

            # 步骤21: 将选中的节点加入Pass
            Pass.add(current_node)

            # 步骤22-24: 检查是否到达目标
            if a_j == tk3:
                print(f"找到路径! 迭代次数: {iteration}")
                return c_j

            # 步骤25-34: 处理当前节点的邻居
            alpha_j = DX.get(a_j)
            if alpha_j is None:
                continue

            # 步骤26: 解密当前节点的DX值
            add_j_encrypted, K_j_encrypted = alpha_j
            add_j = add_j_encrypted ^ b_j
            K_j = K_j_encrypted ^ b_j

            # 获取当前节点的所有邻居
            current_add = add_j
            neighbors_j = []

            while current_add is not None:
                if current_add not in Arr:
                    break

                beta_l, r_l = Arr[current_add]
                H_value_j = RandomOracle.H((str(K_j), str(r_l)))
                N_l = tuple(
                    x ^ H_value_j if isinstance(x, int) else x
                    for x in beta_l
                )

                a_l, b_l, c_l, next_add = N_l
                neighbors_j.append((a_l, b_l, c_l))

                current_add = next_add

            # 步骤35-43: 更新UPass中的距离
            updated_upass = []
            for upass_item in UPass:
                a_i, b_i, c_i = upass_item

                # 步骤36: 检查(a_i, b_i)是否是当前节点的邻居
                is_neighbor = False
                c_i_prime = None
                for a_l, b_l, c_l in neighbors_j:
                    if a_l == a_i and b_l == b_i:
                        is_neighbor = True
                        c_i_prime = c_l
                        break

                if is_neighbor and c_i_prime is not None:
                    # 步骤38: 计算新距离并比较
                    new_c_i = SAP(c_j, c_i_prime, self.pk)

                    # 步骤39: 使用SCP比较新距离和原距离
                    if self.scp.compare(new_c_i, c_i):
                        # 步骤40: 更新距离
                        updated_upass.append((a_i, b_i, new_c_i))
                    else:
                        updated_upass.append(upass_item)
                else:
                    updated_upass.append(upass_item)

            UPass = updated_upass

            # 将当前节点的未处理邻居加入UPass
            for a_l, b_l, c_l in neighbors_j:
                neighbor_node = (a_l, b_l)
                if neighbor_node not in Pass and not any(item[0] == a_l and item[1] == b_l for item in UPass):
                    UPass.append((a_l, b_l, c_l))

        print(f"查询失败: 未找到路径 (迭代: {iteration})")
        return None

    def _sort_upass_by_distance(self, UPass):
        """对UPass按距离排序 - 使用SCP协议进行安全比较"""
        if len(UPass) <= 1:
            return UPass

        # 使用插入排序，每次比较使用SCP协议
        sorted_list = [UPass[0]]

        for i in range(1, len(UPass)):
            current_item = UPass[i]
            inserted = False

            for j in range(len(sorted_list)):
                # 使用SCP比较距离
                if self.scp.compare(current_item[2], sorted_list[j][2]):
                    sorted_list.insert(j, current_item)
                    inserted = True
                    break

            if not inserted:
                sorted_list.append(current_item)

        return sorted_list

    def _generate_permutation(self, size):
        """生成置换函数"""

        class Permutation:
            def __init__(self, size):
                self.size = size
                self.perm = list(range(1, size + 1))
                py_random.shuffle(self.perm)
                self.inv_perm = [0] * (size + 1)
                for i, val in enumerate(self.perm):
                    self.inv_perm[val] = i + 1

            def apply(self, x):
                if 1 <= x <= self.size:
                    return self.perm[x - 1]
                return x

            def inverse_apply(self, x):
                if 1 <= x <= self.size:
                    return self.inv_perm[x]
                return x

        return Permutation(size)

    def _calculate_storage_cost(self, encrypted_graph):
        """计算存储成本"""
        DX = encrypted_graph["DX"]
        Arr = encrypted_graph["Arr"]

        dx_size = len(DX) * (32 + 32 + 32)  # key + add + K
        arr_size = len(Arr) * (32 + 32 + 256 + 32 + 32)  # key + encrypted_N_i + r_i

        total_bytes = dx_size + arr_size
        return total_bytes / (1024 * 1024)


def generate_random_directed_graph(num_vertices=1000, num_edges=10000):
    """高效生成随机有向图（避免内存爆炸）"""
    print(f"生成随机有向图: {num_vertices}个顶点, 目标{num_edges}条边")

    max_possible_edges = num_vertices * (num_vertices - 1)
    num_edges = min(num_edges, max_possible_edges)
    print(f"最大可能边数: {max_possible_edges}, 实际生成{num_edges}条边")

    # 顶点用整数表示（比字符串更高效）
    vertices = list(range(num_vertices))
    graph = {v: {} for v in vertices}
    edges_set = set()  # 用哈希集快速判断边是否重复（存储(u, v)元组）

    edges_added = 0
    # 循环生成边，直到达到目标数量
    while edges_added < num_edges:
        u = py_random.choice(vertices)
        v = py_random.choice(vertices)
        if u != v and (u, v) not in edges_set:  # 排除自环和重复边
            weight = py_random.randint(1, 100)
            graph[u][v] = weight
            edges_set.add((u, v))
            edges_added += 1
            # 进度提示（每1000条边）
            if edges_added % 1000 == 0:
                print(f"已生成 {edges_added}/{num_edges} 条边")

    print(f"图生成完成: 成功生成 {edges_added} 条边")
    return graph

def test_gesdq_large_graph():
    """测试GESDQ方案在大型随机图上的性能"""
    print("=== GESDQ方案大型图测试 ===\n")

    # 生成随机有向图
    num_vertices = 10
    num_edges = 100
    test_graph = generate_random_directed_graph(num_vertices, num_edges)

    # 初始化GESDQ系统
    gesdq = GESDQ(secparam=1024)

    # 加密图
    print("\n步骤1: 加密图数据")
    start_time = time.time()
    encrypted_graph = gesdq.encrypt_graph(test_graph)
    encrypt_time = time.time() - start_time

    # 获取存储成本
    storage_cost = encrypted_graph.get("storage_cost_MB", 0)

    print(f"图加密完成，耗时: {encrypt_time:.2f}秒, 存储成本: {storage_cost:.2f} MB\n")

    # 执行最短距离查询
    print("步骤2: 执行最短距离查询")

    # 随机选择起点和终点
    vertices = list(test_graph.keys())
    start_node = py_random.choice(vertices)
    end_node = py_random.choice(vertices)

    # 确保起点和终点不同
    while start_node == end_node:
        end_node = py_random.choice(vertices)

    print(f"查询从 {start_node} 到 {end_node} 的最短距离")

    start_time = time.time()
    result = gesdq.shortest_distance_query(start_node, end_node, encrypted_graph)
    query_time = time.time() - start_time

    if result:
        print(f"查询完成: 返回加密距离，查询耗时: {query_time:.2f}秒")
    else:
        print(f"查询失败，查询耗时: {query_time:.2f}秒")

    # 性能统计
    print("\n=== 性能统计 ===")
    print(f"图规模: {num_vertices}个顶点, {num_edges}条边")
    print(f"加密时间: {encrypt_time:.2f}秒")
    print(f"存储成本: {storage_cost:.2f} MB")
    print(f"查询时间: {query_time:.2f}秒")

    return encrypt_time, storage_cost, query_time


if __name__ == "__main__":
    # 测试大型随机图
    test_gesdq_large_graph()
