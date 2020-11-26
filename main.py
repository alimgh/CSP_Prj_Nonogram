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
            self.fix_domain_bounds(c_sublist)
            for var in c_sublist:
                # delta = var.num - len(var.domain) > 1
                # up_bound is excluded
                up_bound = var.domain[0] + var.num
                down_bound = var.domain[-1]
                if down_bound <= up_bound - 1:
                    for i in range(down_bound, up_bound):
                        self.board[i][var.depth_no] = 1

        for c_sublist in self.row_cons:
            self.fix_domain_bounds(c_sublist)
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
                domain = var.domain
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
                domain = var.domain
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

                # checking < self.size for last var. because it's possible last var doesn't need x
                # while checking < self.size and checking < up_bound:
                #     if self.board[var.depth_no][checking] == -1:
                #         var.domain.pop(0)
                #         self.board[var.depth_no][up_bound] = 1
                #         up_bound += 1
                #
                #     elif self.board[var.depth_no][checking] == 1:
                #         tmp_checking = checking
                #         for j in range(checking + 1, down_bound):
                #             self.board[var.depth_no][checking] = 1
                #             var.domain.pop(-1)
                #             # up_bound -= 1
                #             checking += 1
                #         down_bound = tmp_checking
                #     checking += 1

                # var.fix_up_bound(down_bound)
                # var.fix_up_bound(up_bound)
                # if len(var.domain) == 1:
                #     var.val = var.domain[0]
                #     if var.val + var.num < self.size:
                #         self.board[var.depth_no][var.val + var.num] = -1
                #     checking += 1
                #     fix = var.val - 1
                #     while fix >= 0 and self.board[var.depth_no][fix] == 0:
                #         self.board[var.depth_no][fix] = -1
                #         fix -= 1
                #     self.fix_domain_bounds(c_sublist)

                    # # drop last element in domain and x last possible square
                    # j = down_bound - 1
                    # while j >= 0 and self.board[var.depth_no][j] == 1:
                    #     self.board[var.depth_no][var.domain[-1] + var.num - 1] = -1
                    #     var.domain.pop(-1)
                    #     if len(var.domain) == 1:
                    #         var.val = var.domain[0]
                    #         # self.board[var.depth_no][var.domain[0] + var.num] = -1
                    #         # self.fix_domain_bounds(c_sublist)
                    #         break
                    #     j -= 1
                    # # drop first element in domain and x first possible square
                    # j = up_bound
                    # while j < self.size and self.board[var.depth_no][j] == 1:
                    #     self.board[var.depth_no][var.domain[0]] = -1
                    #     var.domain.pop(0)
                    #     if len(var.domain) == 1:
                    #         var.val = var.domain[0]
                    #         # self.board[var.depth_no][var.domain[0] + var.num] = -1
                    #         # self.fix_domain_bounds(c_sublist)
                    #         break
                    #     j += 1

    # class method that only uses in node_consistency
    def fix_domain_bounds(self, c_sublist):
        if len(c_sublist) > 1:
            for i in range(len(c_sublist) - 1):
                # num colored + one x that can't colored = c[i].num
                down_bound = c_sublist[i].domain[0] + c_sublist[i].num
                c_sublist[i + 1].fix_down_bound(down_bound)
                # print("down i", c_sublist[i].num, c_sublist[i].domain)
                # print("down i+1", c_sublist[i + 1].num, c_sublist[i + 1].domain)

            for i in range(len(c_sublist) - 1, 0, -1):
                # num i-1 colored + one x for i that can't be colored = c[i-1].num
                # print("up i", c_sublist[i].num, c_sublist[i].domain)
                # print("up i-1", c_sublist[i-1].num, c_sublist[i-1].domain)
                up_bound = c_sublist[i].domain[-1] - c_sublist[i - 1].num
                c_sublist[i - 1].fix_up_bound(up_bound)

    def is_value_consistent(self, var, val):
        for j in range(val):
            c = 0
            c_var = self.col_cons[j][c]
            c_tmp_num = c_var.num
            for i in range(var.depth_no):
                if c_var.num != c_tmp_num and self.board[i][j] == -1:
                    return False
                if self.board[i][j] == 1:
                    c_tmp_num -= 1
                    if c_tmp_num == 0:
                        c += 1
                        if c < len(self.col_cons[j]):
                            c_var = self.col_cons[j][c]
                            c_tmp_num = c_var.num
                        else:
                            break
            if c_tmp_num != c_var.num:
                return False
            elif c_var.domain[-1] <= var.depth_no:
                return False

        for j in range(val + var.num):
            c = 0
            c_var = self.col_cons[j][c]
            c_tmp_num = c_var.num
            for i in range(var.depth_no):
                if c_var.num != c_tmp_num and self.board[i][j] == -1:
                    if c_tmp_num == 0:
                        c += 1
                        if c < len(self.col_cons[j]):
                            c_var = self.col_cons[j][c]
                            c_tmp_num = c_var.num
                        else:
                            break
                    else:
                        return False
                if self.board[i][j] == 1:
                    c_tmp_num -= 1

            if c_tmp_num < 0:
                return False
            elif c < len(self.col_cons[j]):
                if c_tmp_num == 0:
                    return False

        return True


            # c = 0
            # constraint = self.col_cons[j][c].num + 1
            # temp_val = constraint
            # i = 0
            #
            # while i < var.depth_no:
            #     if (self.board[i][j] == -1 or self.board[i][j] == 0) and temp_val == constraint:
            #         i += 1
            #     elif self.board[i][j] == 1:
            #         if temp_val <= 1:
            #             return False
            #         temp_val -= 1
            #     elif self.board[i][j] == -1:
            #         if temp_val == 1:
            #             c += 1
            #             if c < len(self.col_cons[j]):
            #                 constraint = self.col_cons[j][c]
            #                 temp_val = constraint
            #         else:
            #             return False
            #
            # while c < len(self.col_cons[j]):
            #     if


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
    print(no_selected)
    if no_selected == b_csp.no_vars:
        return b_csp

    var = var_generator.get_next_var()

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
        for i in range(value, value + var.num):
            b_csp.board[var.depth_no][i] = 1
        print(b_csp.board)
        b_csp.node_consistency()

        if var is b_csp.row_cons[var.depth_no][-1]:
            cons = 0
            colored = 0
            y = 0
            while y < b_csp.size and cons < len(b_csp.row_cons[var.depth_no]) and b_csp.board[var.depth_no][y] != 0:
                if b_csp.board[var.depth_no][y] == 1:
                    colored += 1
                elif b_csp.board[var.depth_no][y] == -1:
                    if colored == b_csp.row_cons[var.depth_no][cons].num:
                        colored = 0
                        cons += 1
                    elif colored != 0:
                        break
                y += 1
            #     TODO: fix this if condition and check for cols too
            if (y != b_csp.size and cons != len(b_csp.row_cons[var.depth_no])) or \
                not (cons == len(b_csp.row_cons[var.depth_no]) or
                     (cons == len(b_csp.row_cons[var.depth_no]) - 1 and
                      colored == b_csp.row_cons[var.depth_no][cons].num)):
                reverse_backtrack_step(b_csp, j, value, var, var is b_csp.row_cons[var.depth_no][-1])
                continue

        j_check = value
        while j_check < value + var.num:
            c = 0
            while c < len(b_csp.col_cons[j_check]) and b_csp.col_cons[j_check][c].domain:
                c += 1
            if c != len(b_csp.col_cons[j_check]):
                reverse_backtrack_step(b_csp, j, value, var, var is b_csp.row_cons[var.depth_no][-1])
                break
            j_check += 1
        if j_check != value + var.num:
            continue

        c = 0
        while c < len(b_csp.row_cons[var.depth_no]) and b_csp.row_cons[var.depth_no][c].domain:
            c += 1
        if c != len(b_csp.row_cons[var.depth_no]):
            reverse_backtrack_step(b_csp, j, value, var, var is b_csp.row_cons[var.depth_no][-1])
            continue

        result = backtrack_rec(b_csp, no_selected + 1)
        if result:
            return result
        reverse_backtrack_step(b_csp, j, value, var, var is b_csp.row_cons[var.depth_no][-1])
    return False


def reverse_backtrack_step(b_csp, j, value, var, isLast=False):
    # j_start = j
    print("reversed", j)
    var.val = -1
    j += 1
    if isLast:
        while j < b_csp.size:
            b_csp.board[var.depth_no][j] = 0
            j += 1
    else:
        while j <= value + var.num:
            b_csp.board[var.depth_no][j] = 0
            j += 1
    print(b_csp.board)
    print()
    for c_sublist in b_csp.col_cons:
        for c in c_sublist:
            c.domain = [i for i in range(b_csp.size - c.num + 1)]
    for c_sublist in b_csp.row_cons:
        for c in c_sublist:
            c.domain = [i for i in range(b_csp.size - c.num + 1)]
    b_csp.node_consistency()


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
    csp.node_consistency()
    backtrack(csp)
    for cl in csp.row_cons:
        for el in cl:
            print(el.num, el.domain, el.val)
    print(csp.board)
