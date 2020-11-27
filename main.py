# This is a sample Python script.

# Press Shift+F10 to execute it or replace it with your code.
# Press Double Shift to search everywhere for classes, files, tool windows, actions, and settings.

import numpy as np


class CSP:
    def __init__(self, size):
        self.board = np.zeros((size, size), dtype=int)
        self.row_cons = None
        self.col_cons = None
        self.size = size
        self.no_vars = 0

    # TODO: check -1 for col_cons
    # TODO: remove impossible domains for col_cons
    def node_consistency(self):
        if self.row_cons is None or self.col_cons is None:
            raise Exception("Init Vars")

        for c_sublist in self.col_cons:
            if not self.fix_domain_bounds(c_sublist):
                return
            for var in c_sublist:
                # delta = var.num - len(var.domain) > 1
                # up_bound is excluded
                up_bound = var.domain[0] + var.num
                down_bound = var.domain[-1]
                if down_bound <= up_bound - 1:
                    for i_row in range(down_bound, up_bound):
                        self.board[i_row][var.depth_no] = 1

        for c_sublist in self.row_cons:
            if not self.fix_domain_bounds(c_sublist):
                return
            checking = 0
            for var in c_sublist:
                # up_bound is excluded
                up_bound = var.domain[0] + var.num
                down_bound = var.domain[-1]
                if down_bound <= up_bound - 1:
                    for j in range(down_bound, up_bound):
                        self.board[var.depth_no][j] = 1
                if len(var.domain) == 1:
                    var.val = var.domain[0]
                    continue

        for c_sublist in self.col_cons:
            for var in c_sublist:
                domain = var.domain[:]
                for val in domain:
                    if val > 0 and self.board[val-1][var.depth_no] == 1:
                        var.domain.remove(val)
                    elif val + var.num < self.size and self.board[val+var.num][var.depth_no] == 1:
                        var.domain.remove(val)
                    else:
                        for i in range(val, val + var.num):
                            if self.board[i][var.depth_no] == -1:
                                var.domain.remove(val)
                                break

        for c_sublist in self.row_cons:
            for var in c_sublist:
                domain = var.domain[:]
                for val in domain:
                    if val > 0 and self.board[var.depth_no][val-1] == 1:
                        var.domain.remove(val)
                    elif val + var.num < self.size and self.board[var.depth_no][val+var.num] == 1:
                        var.domain.remove(val)
                    else:
                        for j in range(val, val + var.num):
                            if self.board[var.depth_no][j] == -1:
                                var.domain.remove(val)
                                break


    # class method that only uses in node_consistency
    def fix_domain_bounds(self, c_sublist):
        if len(c_sublist) > 1:
            for check_v in range(len(c_sublist) - 1):
                if not c_sublist[check_v].domain:
                    return False
                # num colored + one x that can't colored = c[i].num
                down_bound = c_sublist[check_v].domain[0] + c_sublist[check_v].num
                c_sublist[check_v + 1].fix_down_bound(down_bound)


            for check_v in range(len(c_sublist) - 1, 0, -1):
                if not c_sublist[check_v].domain:
                    return False
                # num i-1 colored + one x for i that can't be colored = c[i-1].num
                up_bound = c_sublist[check_v].domain[-1] - c_sublist[check_v - 1].num
                c_sublist[check_v - 1].fix_up_bound(up_bound)

        return True


class Var:
    def __init__(self, num, depth_no, size):
        self.num = num
        self.val = -1
        self.depth_no = depth_no
        self.domain = [i for i in range(size-num+1)]

    def set_val(self, val):
        self.val = val

    def fix_up_bound(self, bound):
        self.domain = list(filter(lambda x: x < bound, self.domain))

    def fix_down_bound(self, bound):
        self.domain = list(filter(lambda x: x > bound, self.domain))

    def get_fix_down_bound(self, value, num):
        return list(filter(lambda x: x > value + num, self.domain))


def backtrack(b_csp):
    return backtrack_rec(b_csp, 0)


def backtrack_rec(b_csp, no_selected):
    # print(no_selected)
    if no_selected == b_csp.no_vars:
        if check_col_consistency(b_csp):
            return b_csp
        else:
            return False

    var = var_generator.get_var(no_selected)

    for value in var.domain:
        var.val = value
        var.domain = [value]
        if value + var.num < b_csp.size:
            b_csp.board[var.depth_no][value + var.num] = -1
        # print(var.depth_no, var.num, var is b_csp.row_cons[var.depth_no][-1])
        if var is b_csp.row_cons[var.depth_no][-1]:
            j = value + var.num + 1
            while j < b_csp.size and b_csp.board[var.depth_no][j] == 0:
                b_csp.board[var.depth_no][j] = -1
                j += 1
        j = var.val - 1
        while j >= 0 and b_csp.board[var.depth_no][j] == 0:
            b_csp.board[var.depth_no][j] = -1
            j -= 1
        for v in range(value, value + var.num):
            b_csp.board[var.depth_no][v] = 1
        # print(b_csp.board)
        b_csp.node_consistency()
        # for cl in csp.row_cons:
        #     for el in cl:
        #         print(el.num, el.domain, el.val)

        if var is b_csp.row_cons[var.depth_no][-1]:
            cons = 0
            colored = 0
            y = 0
            while y < b_csp.size and b_csp.board[var.depth_no][y] != 0:
                if b_csp.board[var.depth_no][y] == 1:
                    colored += 1
                    if cons == len(b_csp.row_cons[var.depth_no]):
                        break
                elif b_csp.board[var.depth_no][y] == -1:
                    if cons < len(b_csp.row_cons[var.depth_no]) and colored == b_csp.row_cons[var.depth_no][cons].num:
                        colored = 0
                        cons += 1
                    elif colored != 0:
                        break
                y += 1
            if cons == len(b_csp.row_cons[var.depth_no]):
                cons -= 1
            # TODO: fix this if condition and check for cols too
            if not (y == b_csp.size and cons == len(b_csp.row_cons[var.depth_no]) - 1
                    and (colored == 0 or colored == b_csp.row_cons[var.depth_no][cons].num)):
                reverse_backtrack_step(b_csp, j, value, var, var is b_csp.row_cons[var.depth_no][-1])
                continue

        j_check = 0
        while j_check < b_csp.size:
            c = 0
            while c < len(b_csp.col_cons[j_check]) and b_csp.col_cons[j_check][c].domain:
                c += 1
            if c != len(b_csp.col_cons[j_check]):
                break
            j_check += 1
        if j_check != b_csp.size:
            reverse_backtrack_step(b_csp, j, value, var, var is b_csp.row_cons[var.depth_no][-1])
            continue

        i_check = 0
        while i_check < b_csp.size:
            c = 0
            while c < len(b_csp.row_cons[i_check]) and b_csp.row_cons[i_check][c].domain:
                c += 1
            if c != len(b_csp.row_cons[i_check]):
                break
            i_check += 1
        if i_check != b_csp.size:
            reverse_backtrack_step(b_csp, j, value, var, var is b_csp.row_cons[var.depth_no][-1])
            continue

        result = backtrack_rec(b_csp, no_selected + 1)
        if result:
            return result
        reverse_backtrack_step(b_csp, j, value, var, var is b_csp.row_cons[var.depth_no][-1])
    return False


def reverse_backtrack_step(b_csp, j, value, var, isLast=False):
    # j_start = j
    # print("reversed", j)
    var.val = -1
    j += 1
    # if isLast:
    while j < b_csp.size:
        b_csp.board[var.depth_no][j] = 0
        j += 1
    # else:
    #     while j <= value + var.num:
    #         b_csp.board[var.depth_no][j] = 0
    #         j += 1
    for row in range(var.depth_no+1, b_csp.size):
        for col in range(b_csp.size):
            b_csp.board[row][col] = 0
    for c_sublist in b_csp.col_cons:
        for c in c_sublist:
            c.domain = [i for i in range(b_csp.size - c.num + 1)]
    for c_sublist in b_csp.row_cons:
        for c in c_sublist:
            c.domain = [i for i in range(b_csp.size - c.num + 1)]
    b_csp.node_consistency()
    # print(b_csp.board)
    # print()


def check_col_consistency(b_csp):
    for j in range(b_csp.size):
        cons = 0
        colored = 0
        x = 0
        while x < b_csp.size and b_csp.board[x][j] != 0:
            if b_csp.board[x][j] == 1:
                colored += 1
                if cons == len(b_csp.col_cons[j]):
                    break
            elif b_csp.board[x][j] == -1:
                if cons < len(b_csp.col_cons[j]) and colored == b_csp.col_cons[j][cons].num:
                    colored = 0
                    cons += 1
                elif colored != 0:
                    break
            x += 1
        if cons == len(b_csp.col_cons[j]):
            cons -= 1
        if not (x == b_csp.size and cons == len(b_csp.col_cons[j]) - 1
                and (colored == 0 or colored == b_csp.col_cons[j][cons].num)):
            return False
    return True


class VarGenerator:
    def __init__(self, var_list, no_vars):
        self.var_list = np.empty(no_vars, dtype=object)
        self.idx = 0
        for sub_list in var_list:
            for e in sub_list:
                self.var_list[self.idx] = e
                self.idx += 1
        self.idx = 0

    def get_next_var(self):
        next_var = self.var_list[self.idx]
        self.idx += 1
        return next_var

    def get_var(self, idx):
        return self.var_list[idx]


if __name__ == '__main__':
    n = int(input())

    csp = CSP(n)

    tmp = []
    for d in range(n):
        constraints = input().split()
        csp.no_vars += int(constraints[0])
        tmp.append(np.array([Var(int(j), d, n) for j in constraints[1:]]))
    csp.row_cons = np.array(tmp, dtype=object)

    tmp = []
    for d in range(n):
        constraints = input().split()
        tmp.append(np.array([Var(int(j), d, n) for j in constraints[1:]]))
    csp.col_cons = np.array(tmp, dtype=object)

    var_generator = VarGenerator(csp.row_cons, csp.no_vars)
    print("Solving")
    csp.node_consistency()
    if backtrack(csp):
        print(csp.board)
        print()
        for i in csp.board:
            for j in i:
                if j == 1:
                    print('*', end=' ')
                elif j == -1:
                    print('.', end=' ')
            print()
    else:
        print("Failure!")
        print("There is no answer! Please check numbers!")
