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
        self.pk, self.sk = self.KeyGen()


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
    def __init__(self, dtpkc):
        self.dtpkc = dtpkc
        self.csp1_pk, self.csp1_sk = dtpkc.KeyGen()
        self.csp2_pk, self.csp2_sk = dtpkc.KeyGen()

    def compare(self, m1_cipher, m2_cipher):
        N = self.csp1_pk["N"]
        N2 = N * N

        # 步骤1：密文变换
        m1_tilde = {
            "T1": ((m1_cipher["T1"] ** 2) % N2) * (self.csp1_pk["h"] ** 1 % N2) % N2,
            "T2": (m1_cipher["T2"] ** 2) % N2
        }
        m2_tilde = {
            "T1": (m2_cipher["T1"] ** 2) % N2,
            "T2": (m2_cipher["T2"] ** 2) % N2
        }

        # 步骤2：随机位b
        b = random(2)

        # 步骤3：计算比较结果密文
        if b == 1:
            m2_tilde_neg = {
                "T1": (m2_tilde["T1"] ** (N - 1)) % N2,
                "T2": (m2_tilde["T2"] ** (N - 1)) % N2
            }
            res_cipher = SAP(m1_tilde, m2_tilde_neg, self.csp1_pk)
        else:
            m1_tilde_neg = {
                "T1": (m1_tilde["T1"] ** (N - 1)) % N2,
                "T2": (m1_tilde["T2"] ** (N - 1)) % N2
            }
            res_cipher = SAP(m1_tilde_neg, m2_tilde, self.csp1_pk)

        # 步骤4：混淆结果
        r = random(N / 4)
        RES = (res_cipher["T1"] ** r) % N2

        # 步骤5-6：协同解密
        lamda1, lamda2 = self.dtpkc.SplitMK(self.dtpkc.mk)
        RES1 = self.dtpkc.PSDec1(res_cipher, lamda1)
        RES2 = self.dtpkc.PSDec2(res_cipher, lamda2, RES1)

        # 步骤7-8：判断结果
        L_N = bitsize(N)
        L_RES2 = bitsize(RES2)
        flag = 1 if L_RES2 > (L_N / 2) else 0
        return flag == 1 if b == 0 else flag == 1



class PRF:
    """伪随机函数实现 - 使用HMAC-SHA256"""

    def __init__(self, key):
        # 将key转换为bytes
        if isinstance(key, integer):
            self.key = str(int(key)).encode()
        elif isinstance(key, str):
            self.key = key.encode()
        else:
            self.key = str(key).encode()

    def evaluate(self, x):
        """计算F_key(x) - 修复性能问题"""
        # 将输入x转换为bytes
        if isinstance(x, integer):
            x_bytes = str(int(x)).encode()
        elif isinstance(x, str):
            x_bytes = x.encode()
        else:
            x_bytes = str(x).encode()

        h = hashlib.pbkdf2_hmac('sha256', x_bytes, self.key, 100000)
        return int.from_bytes(h[:16], 'big')  # 取前16字节作为输出


class RandomOracle:
    """随机预言机实现 - 使用SHA256"""

    @staticmethod
    def H(data):
        """随机预言机H - 修复性能问题"""
        if isinstance(data, tuple):
            # 将元组中的所有元素转换为字符串并连接
            data_str = ''.join(str(x) for x in data)
        else:
            data_str = str(data)
        # 使用更快的哈希函数
        return int(hashlib.sha256(data_str.encode()).hexdigest(), 16)


class Permutation:
    """随机置换实现"""

    def __init__(self, size):
        self.size = size
        # 生成随机置换
        indices = list(range(1, size + 1))
        import random as py_random
        py_random.shuffle(indices)
        self.permutation = {i: indices[i - 1] for i in range(1, size + 1)}
        self.inverse = {v: k for k, v in self.permutation.items()}

    def apply(self, x):
        """应用置换π(x)"""
        return self.permutation.get(x, x)

    def inverse_apply(self, x):
        """应用逆置换π^{-1}(x)"""
        return self.inverse.get(x, x)

class GESDQ:
    """GESDQ图加密方案 - 严格按照论文要求实现"""

    def __init__(self, secparam=1024):
        print("初始化GESDQ系统...")
        self.secparam = secparam
        self.dtpkc = DTPKC(secparam)
        self.scp = SCP(self.dtpkc)
        self.pk = self.dtpkc.pk

        self.DX = {}
        self.Arr = {}
        self.pi = None

        # 创建密文池：权重1-100
        print("生成密文池...")
        self.max_weight = 100
        self.cipher_pool = {}
        for weight in range(1, self.max_weight + 1):
            self.cipher_pool[weight] = self.dtpkc.Encrypt(self.pk, integer(weight))

        pool_size_bytes = len(self.cipher_pool) * (self.secparam // 8) * 2  # 每个密文约256字节
        print(f"密文池: {len(self.cipher_pool)}个密文, 约{pool_size_bytes / 1024:.1f} KB")
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
        self.pi = Permutation(M)

        # 生成密钥
        self.k1 = py_random.getrandbits(128)
        self.k2 = py_random.getrandbits(128)

        prf_k1 = PRF(self.k1)
        prf_k2 = PRF(self.k2)

        ctr = 1

        # 处理每个顶点
        for i, u in enumerate(V):
            if i % 100 == 0 and N > 100:
                print(f"加密进度: {i}/{N} 个顶点")

            # 为每个顶点生成密钥K_u
            K_u = py_random.getrandbits(128)
            neighbors = list(graph[u].items())

            # 处理每个邻居
            for j, (v, dis_uv) in enumerate(neighbors):
                # 验证权重范围
                if dis_uv < 1 or dis_uv > self.max_weight:
                    raise ValueError(f"边权重 {dis_uv} 超出范围 [1, {self.max_weight}]")

                # 使用权重ID而不是完整密文
                weight_id = int(dis_uv)

                # 计算邻居标识符
                a_i = prf_k1.evaluate(v)
                b_i = prf_k2.evaluate(v)

                # 计算下一个指针
                if j < len(neighbors) - 1:
                    next_add = self.pi.apply(ctr + 1)
                else:
                    next_add = 0  # 0表示链表结束

                # 二进制打包N_i：a_i(8) + b_i(8) + weight_id(2) + next_add(4) = 22字节
                try:
                    N_i_bytes = struct.pack('>QQHI',
                                            a_i & 0xFFFFFFFFFFFFFFFF,
                                            b_i & 0xFFFFFFFFFFFFFFFF,
                                            weight_id,  # 使用2字节存储权重ID
                                            next_add)
                except struct.error as e:
                    print(f"打包错误: a_i={a_i}, b_i={b_i}, weight_id={weight_id}, next_add={next_add}")
                    raise e

                # 生成随机数r_i
                r_i = py_random.getrandbits(128)

                # 使用H(K_u || r_i)加密N_i字节串
                H_value = RandomOracle.H((str(K_u), str(r_i)))

                # 生成与N_i_bytes等长的密钥流
                key_stream = b''
                for k in range(len(N_i_bytes)):
                    key_byte = (H_value >> (8 * (k % 8))) & 0xFF
                    key_stream += bytes([key_byte])

                # XOR加密
                encrypted_bytes = bytes([N_i_bytes[k] ^ key_stream[k] for k in range(len(N_i_bytes))])

                # 存储到Arr中
                self.Arr[self.pi.apply(ctr)] = (encrypted_bytes, r_i)
                ctr += 1

            # 设置DX条目
            if neighbors:
                add_N1 = self.pi.apply(ctr - len(neighbors))  # 第一个邻居的地址

                # 二进制打包DX值：add_N1(4) + K_u(16) = 20字节
                DX_value_bytes = struct.pack('>IQQ',
                                             add_N1,
                                             K_u & 0xFFFFFFFFFFFFFFFF,
                                             (K_u >> 64) & 0xFFFFFFFFFFFFFFFF)

                # 使用F_k2(u)加密DX值
                u_hash = prf_k2.evaluate(u)
                key_stream = b''
                for k in range(len(DX_value_bytes)):
                    key_byte = (u_hash >> (8 * (k % 8))) & 0xFF
                    key_stream += bytes([key_byte])

                encrypted_DX = bytes([DX_value_bytes[k] ^ key_stream[k] for k in range(len(DX_value_bytes))])
                self.DX[prf_k1.evaluate(u) & 0xFFFFFFFFFFFFFFFF] = encrypted_DX

        encrypted_graph = {
            "DX": self.DX,
            "Arr": self.Arr,
            "cipher_pool": self.cipher_pool,
            "pi": self.pi,
            "k1": self.k1,
            "k2": self.k2
        }

        storage_info = self._calculate_storage_cost(encrypted_graph)
        encrypted_graph["storage_info"] = storage_info

        print(f"图加密完成: {N}个顶点, {M}条边")
        print(f"存储成本详情:")
        print(f"  - 密文池: {storage_info['pool_KB']:.2f} KB")
        print(f"  - DX索引: {storage_info['dx_KB']:.2f} KB")
        print(f"  - Arr数组: {storage_info['arr_KB']:.2f} KB")
        print(f"  - 总计: {storage_info['total_KB']:.2f} KB")
        return encrypted_graph

    def shortest_distance_query(self, u, v, encrypted_graph):
        """最短距离查询 - 严格按照算法2实现，使用SCP比较距离"""
        print(f"执行查询: {u} -> {v}")

        DX = encrypted_graph["DX"]
        Arr = encrypted_graph["Arr"]
        cipher_pool = encrypted_graph["cipher_pool"]
        k1 = encrypted_graph["k1"]
        k2 = encrypted_graph["k2"]

        prf_k1 = PRF(k1)
        prf_k2 = PRF(k2)

        # 步骤1: 计算令牌
        tk1 = prf_k1.evaluate(u)
        tk2 = prf_k2.evaluate(u)
        tk3 = prf_k1.evaluate(v)

        print(f"令牌计算: tk1={tk1 & 0xFFFF}, tk2={tk2 & 0xFFFF}, tk3={tk3 & 0xFFFF}")

        # 步骤3: 查找起点和终点
        alpha_u = DX.get(tk1 & 0xFFFFFFFFFFFFFFFF)
        alpha_v = DX.get(tk3 & 0xFFFFFFFFFFFFFFFF)

        if alpha_u is None:
            print(f"错误: 未找到起点 {u} 在DX中")
            available_keys = [k & 0xFFFF for k in list(DX.keys())[:5]]
            print(f"DX中前5个键: {available_keys}")
            return None

        if alpha_v is None:
            print(f"错误: 未找到终点 {v} 在DX中")
            return None

        print("找到起点和终点在DX中")

        # 步骤7: 初始化集合
        Pass = set()
        UPass = []  # 列表存储 (a_i, b_i, c_i)

        # 步骤8: 将起点加入Pass
        start_node = (prf_k1.evaluate(u), prf_k2.evaluate(u))
        Pass.add(start_node)

        # 步骤9-18: 处理起点的邻居
        # 解密DX值获取起始地址和密钥
        DX_bytes = alpha_u
        decrypted_DX = bytes([DX_bytes[i] ^ ((tk2 >> (8 * (i % 8))) & 0xFF)
                              for i in range(len(DX_bytes))])

        # 解包DX值
        add_start, K_u_low, K_u_high = struct.unpack('>IQQ', decrypted_DX)
        K_u = (K_u_high << 64) | K_u_low

        current_add = add_start
        iteration_count = 0

        # 遍历邻居链表
        while current_add != 0 and iteration_count < 1000:  # 防止无限循环
            iteration_count += 1

            if current_add not in Arr:
                print(f"警告: 地址 {current_add} 不在Arr中")
                break

            # 获取加密的邻居数据
            encrypted_bytes, r_i = Arr[current_add]

            # 解密邻居数据
            H_value = RandomOracle.H((str(K_u), str(r_i)))
            key_stream = b''
            for k in range(len(encrypted_bytes)):
                key_byte = (H_value >> (8 * (k % 8))) & 0xFF
                key_stream += bytes([key_byte])

            decrypted_bytes = bytes([encrypted_bytes[k] ^ key_stream[k]
                                     for k in range(len(encrypted_bytes))])

            # 解包邻居数据
            a_i, b_i, weight_id, next_add = struct.unpack('>QQHI', decrypted_bytes)

            # 从密文池获取加密距离
            if weight_id not in cipher_pool:
                print(f"错误: 权重ID {weight_id} 不在密文池中")
                c_i = self.dtpkc.Encrypt(self.pk, integer(1))  # 使用默认值
            else:
                c_i = cipher_pool[weight_id]

            # 步骤14: 将邻居加入UPass
            UPass.append((a_i, b_i, c_i))

            current_add = next_add

        print(f"初始UPass大小: {len(UPass)}")

        # 步骤19-44: 主循环
        iteration = 0
        max_iterations = min(1000, len(UPass) * 10)  # 防止无限循环

        while UPass and iteration < max_iterations:
            iteration += 1

            # 步骤20: 使用SCP协议找到UPass中距离最小的节点
            min_item = self._find_min_distance_with_scp(UPass)
            if min_item is None:
                break

            # 步骤21: 选择距离最小的节点
            a_j, b_j, c_j = min_item

            # 从UPass中移除最小节点
            UPass = [item for item in UPass if item != min_item]

            current_node = (a_j, b_j)

            # 步骤21: 将选中的节点加入Pass
            Pass.add(current_node)

            # 步骤22-24: 检查是否到达目标
            if a_j == (tk3 & 0xFFFFFFFFFFFFFFFF):
                print(f"找到路径! 迭代次数: {iteration}")
                return c_j

            # 步骤25-34: 处理当前节点的邻居
            alpha_j = DX.get(a_j)
            if alpha_j is None:
                continue

            # 解密当前节点的DX值
            DX_bytes_j = alpha_j
            decrypted_DX_j = bytes([DX_bytes_j[i] ^ ((b_j >> (8 * (i % 8))) & 0xFF)
                                    for i in range(len(DX_bytes_j))])
            add_j, K_j_low, K_j_high = struct.unpack('>IQQ', decrypted_DX_j)
            K_j = (K_j_high << 64) | K_j_low

            # 获取当前节点的所有邻居
            current_add_j = add_j
            neighbors_j = []
            neighbor_iteration = 0

            while current_add_j != 0 and neighbor_iteration < 1000:
                neighbor_iteration += 1

                if current_add_j not in Arr:
                    break

                encrypted_bytes_l, r_l = Arr[current_add_j]
                H_value_j = RandomOracle.H((str(K_j), str(r_l)))

                key_stream_j = b''
                for k in range(len(encrypted_bytes_l)):
                    key_byte = (H_value_j >> (8 * (k % 8))) & 0xFF
                    key_stream_j += bytes([key_byte])

                decrypted_bytes_j = bytes([encrypted_bytes_l[k] ^ key_stream_j[k]
                                           for k in range(len(encrypted_bytes_l))])

                a_l, b_l, weight_id_l, next_add_j = struct.unpack('>QQHI', decrypted_bytes_j)

                if weight_id_l in cipher_pool:
                    c_l = cipher_pool[weight_id_l]
                    neighbors_j.append((a_l, b_l, c_l))
                else:
                    print(f"警告: 权重ID {weight_id_l} 不在密文池中")

                current_add_j = next_add_j

            # 步骤35-43: 更新UPass中的距离
            updated_upass = []
            for upass_item in UPass:
                a_i, b_i, c_i = upass_item

                # 检查当前节点是否有到该邻居的边
                edge_found = False
                edge_distance = None

                for a_n, b_n, c_n in neighbors_j:
                    if a_n == a_i and b_n == b_i:
                        edge_found = True
                        edge_distance = c_n
                        break

                if edge_found:
                    # 计算新距离: c_j + edge_distance
                    new_c_i = SAP(c_j, edge_distance, self.pk)

                    # 使用SCP比较新距离和原距离
                    if self.scp.compare(new_c_i, c_i):
                        # 新距离更小，更新
                        updated_upass.append((a_i, b_i, new_c_i))
                    else:
                        updated_upass.append(upass_item)
                else:
                    updated_upass.append(upass_item)

            UPass = updated_upass

            # 将当前节点的未处理邻居加入UPass
            for a_l, b_l, c_l in neighbors_j:
                neighbor_key = (a_l, b_l)
                if neighbor_key not in Pass and not any(item[0] == a_l and item[1] == b_l for item in UPass):
                    UPass.append((a_l, b_l, c_l))

        print(f"查询失败: 未找到路径 (迭代: {iteration})")
        return None

    def _find_min_distance_with_scp(self, UPass):
        """使用SCP协议找到UPass中距离最小的节点"""
        if not UPass:
            return None

        if len(UPass) == 1:
            return UPass[0]

        # 对于小规模UPass，使用完整比较
        if len(UPass) <= 10:
            min_item = UPass[0]
            for i in range(1, len(UPass)):
                # 使用SCP比较当前最小项和第i项
                if self.scp.compare(UPass[i][2], min_item[2]):
                    min_item = UPass[i]
            return min_item

        # 对于大规模UPass，使用分批处理优化性能
        # 将UPass分成小批次，每批找到最小值，然后比较批次最小值
        batch_size = 10
        batches = [UPass[i:i + batch_size] for i in range(0, len(UPass), batch_size)]

        batch_mins = []
        for batch in batches:
            batch_min = batch[0]
            for item in batch[1:]:
                if self.scp.compare(item[2], batch_min[2]):
                    batch_min = item
            batch_mins.append(batch_min)

        # 比较所有批次的最小值
        final_min = batch_mins[0]
        for batch_min in batch_mins[1:]:
            if self.scp.compare(batch_min[2], final_min[2]):
                final_min = batch_min

        return final_min

    def _update_upass_distances_with_scp(self, UPass, from_node, neighbors, pk):
        """使用SCP协议更新UPass中的距离"""
        updated_upass = []

        for upass_item in UPass:
            a_i, b_i, c_i = upass_item

            # 查找从当前节点到UPass节点的边
            edge_distance = None
            for a_n, b_n, c_n in neighbors:
                if a_n == a_i and b_n == b_i:
                    edge_distance = c_n
                    break

            if edge_distance is not None:
                # 计算新距离: from_node距离 + 边距离
                new_distance = SAP(from_node[2], edge_distance, pk)

                # 使用SCP比较新距离和原距离
                if self.scp.compare(new_distance, c_i):
                    # 新距离更小，更新
                    updated_upass.append((a_i, b_i, new_distance))
                else:
                    updated_upass.append(upass_item)
            else:
                updated_upass.append(upass_item)

        return updated_upass

    def _calculate_storage_cost(self, encrypted_graph):
        """计算精确的存储成本"""
        DX = encrypted_graph["DX"]
        Arr = encrypted_graph["Arr"]
        cipher_pool = encrypted_graph["cipher_pool"]

        # 密文池成本
        cipher_bytes_per_item = (self.secparam // 8) * 2  # 每个密文约256字节
        pool_bytes = len(cipher_pool) * cipher_bytes_per_item

        # DX成本: 键(8字节) + 值(20字节) = 28字节每项
        dx_bytes = len(DX) * 28

        # Arr成本: 键(4字节) + 加密数据(22字节) + r_i(16字节) = 42字节每项
        arr_bytes = len(Arr) * 42

        total_bytes = pool_bytes + dx_bytes + arr_bytes

        return {
            "pool_KB": pool_bytes / 1024,
            "dx_KB": dx_bytes / 1024,
            "arr_KB": arr_bytes / 1024,
            "total_KB": total_bytes / 1024,
            "per_edge_bytes": arr_bytes / len(Arr) if len(Arr) > 0 else 0,
            "pool_items": len(cipher_pool),
            "dx_items": len(DX),
            "arr_items": len(Arr)
        }


def load_graph_from_file(filename):
    """
    从文件加载图数据（Bitcoin OTC信任网络）
    文件格式：source target weight timestamp

    处理规则：
    - 正权重：表示信任，保留并映射到1-100
    - 负权重：表示不信任，跳过
    - 零权重：跳过

    Args:
        filename: 数据文件路径

    Returns:
        graph: 图字典 {node: {neighbor: weight}}
    """
    print(f"\n从文件加载图: {filename}")

    graph = {}
    edge_count = 0
    skipped_count = 0
    weight_stats = {'min': float('inf'), 'max': float('-inf'), 'sum': 0, 'count': 0}

    try:
        with open(filename, 'r', encoding='utf-8') as f:
            for line_num, line in enumerate(f, 1):
                line = line.strip()

                # 跳过注释和空行
                if not line or line.startswith('#'):
                    continue

                # 分割数据（制表符或空格）
                parts = line.split()
                if len(parts) < 3:
                    continue

                try:
                    source = str(parts[0])
                    target = str(parts[1])
                    weight = int(float(parts[2]))
                    # parts[3] 是时间戳，忽略

                    # 只保留正权重（信任关系）
                    if weight <= 0:
                        skipped_count += 1
                        continue

                    # 限制权重在1-100范围
                    # 如果原始权重是1-10，可以乘以10扩展
                    if weight <= 10:
                        weight = weight * 10  # 1-10 → 10-100
                    weight = max(1, min(100, weight))

                    # 更新统计
                    weight_stats['min'] = min(weight_stats['min'], weight)
                    weight_stats['max'] = max(weight_stats['max'], weight)
                    weight_stats['sum'] += weight
                    weight_stats['count'] += 1

                    # 构建图
                    if source not in graph:
                        graph[source] = {}

                    # 如果存在重复边，保留第一个
                    if target not in graph[source]:
                        graph[source][target] = weight
                        edge_count += 1

                except (ValueError, IndexError) as e:
                    print(f"警告: 第{line_num}行解析错误，跳过: {line[:50]}")
                    continue

        # 确保所有节点都有条目（包括只有入边的节点）
        all_nodes = set(graph.keys())
        for neighbors in graph.values():
            all_nodes.update(neighbors.keys())

        for node in all_nodes:
            if node not in graph:
                graph[node] = {}  # 只有入边，无出边

        num_vertices = len(graph)

        print(f"✓ 加载完成:")
        print(f"  节点数: {num_vertices}")
        print(f"  有效边数: {edge_count} (正权重)")
        print(f"  跳过边数: {skipped_count} (负权重/零权重)")

        if weight_stats['count'] > 0:
            avg_weight = weight_stats['sum'] / weight_stats['count']
            print(f"  权重范围: {weight_stats['min']} - {weight_stats['max']}")
            print(f"  平均权重: {avg_weight:.1f}")

        return graph

    except FileNotFoundError:
        print(f"\n✗ 错误: 文件不存在 - {filename}")
        print(f"  请确保文件在当前目录下")
        return None
    except Exception as e:
        print(f"\n✗ 错误: 读取文件失败 - {e}")
        return None


def test_gesdq_large_graph():
    """测试GESDQ方案 - 使用真实数据"""
    print("=" * 60)
    print("  GESDQ加密图查询测试 - Bitcoin OTC信任网络")
    print("=" * 60)

    # 从文件加载图数据
    data_file = "soc-sign-bit/home/ubuntu/PycharmProjects/pythonProject/soc-sign-bitcoinotc.csv"
    test_graph = load_graph_from_file(data_file)

    if test_graph is None:
        print("\n✗ 数据加载失败，程序退出")
        return None, None, None

    if len(test_graph) == 0:
        print("\n✗ 图为空，程序退出")
        return None, None, None

    # 初始化GESDQ系统
    print("\n" + "=" * 60)
    print("  初始化加密系统")
    print("=" * 60)
    gesdq = GESDQ(secparam=1024)

    # 加密图
    print("\n" + "=" * 60)
    print("  步骤1: 加密图数据")
    print("=" * 60)
    start_time = time.time()
    encrypted_graph = gesdq.encrypt_graph(test_graph)
    encrypt_time = time.time() - start_time

    storage_info = encrypted_graph.get("storage_info", {})
    print(f"\n✓ 图加密完成，耗时: {encrypt_time:.2f}秒")

    # 执行最短距离查询
    print("\n" + "=" * 60)
    print("  步骤2: 执行最短距离查询")
    print("=" * 60)

    # 选择起点和终点
    vertices = list(test_graph.keys())

    # 选择有出边的节点作为起点
    valid_sources = [v for v in vertices if test_graph[v]]
    if not valid_sources:
        print("✗ 没有有效的源节点")
        return encrypt_time, storage_info.get('total_KB', 0), None

    start_node = py_random.choice(valid_sources)
    end_node = py_random.choice(vertices)

    # 确保起点和终点不同
    attempts = 0
    while start_node == end_node and attempts < 100:
        end_node = py_random.choice(vertices)
        attempts += 1

    print(f"\n查询路径: {start_node} → {end_node}")

    start_time = time.time()
    result = gesdq.shortest_distance_query(start_node, end_node, encrypted_graph)
    query_time = time.time() - start_time

    # 输出结果
    print("\n" + "=" * 60)
    print("  查询结果")
    print("=" * 60)

    if result:
        print(f"✓ 查询成功")
        print(f"  查询耗时: {query_time:.2f}秒")

        # 解密结果
        try:
            decrypted_distance = gesdq.dtpkc.DecryptMK(result, gesdq.dtpkc.mk)
            print(f"  解密距离: {decrypted_distance}")
        except Exception as e:
            print(f"✗ 解密失败: {e}")
    else:
        print(f"✗ 查询失败（未找到路径）")
        print(f"  查询耗时: {query_time:.2f}秒")

    # 性能统计
    num_vertices = len(test_graph)
    num_edges = sum(len(neighbors) for neighbors in test_graph.values())
    print("  性能统计")
    print(f"数据集: Bitcoin OTC信任网络")
    print(f"图规模: {num_vertices}个顶点, {num_edges}条边")
    print(f"安全参数: {gesdq.secparam} 位")
    print(f"\n时间成本:")
    print(f"  加密时间: {encrypt_time:.2f}秒")
    print(f"  查询时间: {query_time:.2f}秒")
    print(f"\n存储成本: {storage_info.get('total_KB', 0):.2f} KB ({storage_info.get('total_KB', 0) / 1024:.3f} MB)")

    return encrypt_time, storage_info.get('total_KB', 0), query_time


if __name__ == "__main__":
    test_gesdq_large_graph()


