# This is a sample Python script.

# Press Shift+F10 to execute it or replace it with your code.
# Press Double Shift to search everywhere for classes, files, tool windows, actions, and settings.

import numpy as np
import time


class CSP:
	def __init__(self, size):
		"""
		CSP problem
		:param size: size of board
		:arg self.board: array of board. (0:empty, 1:colored, -1:crossed)
		:arg self.row_cons: row Vars. It's an array of arrays and each array contains vars of that row
		:arg self.col_cons: It's like row_cons and contains columns consistencies.
							In this algorithm we work with consistencies just like rows' vars
		"""
		self.board = np.zeros((size, size), dtype=int)
		self.row_cons = None
		self.col_cons = None
		self.size = size
		self.no_vars = 0

	'''checking if value is consistent in var.domain'''

	def node_consistency(self):
		if self.row_cons is None or self.col_cons is None:
			raise Exception("Init Vars")

		'''
		fixing cols and rows vars domain by removing impossible values
		and coloring certain cells in board
		'''
		for c_sublist in self.col_cons:
			if not self.fix_domain_bounds(c_sublist):
				return
			for var in c_sublist:
				# up_bound is excluded
				up_bound = min(var.domain) + var.num
				down_bound = max(var.domain)
				if down_bound <= up_bound - 1:
					for i_row in range(down_bound, up_bound):
						self.board[i_row][var.depth_no] = 1

		for c_sublist in self.row_cons:
			if not self.fix_domain_bounds(c_sublist):
				return
			for var in c_sublist:
				# up_bound is excluded
				up_bound = min(var.domain) + var.num
				down_bound = max(var.domain)
				if down_bound <= up_bound - 1:
					for j in range(down_bound, up_bound):
						self.board[var.depth_no][j] = 1

		'''
		now removing impossible values according new domain and colored cells
		we remove a value in 2 condition
		1. If we choose that value, colored cells exceed variable's number (2 first if)
		2. There is a cross in range of value coloring cells.(can't color all cells)
		'''
		for c_sublist in self.col_cons:
			for var in c_sublist:
				domain = var.domain[:]
				for val in domain:
					if val > 0 and self.board[val - 1][var.depth_no] == 1:
						var.domain.remove(val)
					elif val + var.num < self.size and self.board[val + var.num][var.depth_no] == 1:
						var.domain.remove(val)
					else:
						for r in range(val, val + var.num):
							if self.board[r][var.depth_no] == -1:
								var.domain.remove(val)
								break

		for c_sublist in self.row_cons:
			for var in c_sublist:
				domain = var.domain[:]
				for val in domain:
					if val > 0 and self.board[var.depth_no][val - 1] == 1:
						var.domain.remove(val)
					elif val + var.num < self.size and self.board[var.depth_no][val + var.num] == 1:
						var.domain.remove(val)
					else:
						for j in range(val, val + var.num):
							if self.board[var.depth_no][j] == -1:
								var.domain.remove(val)
								break

	# class method that only uses in node_consistency
	def fix_domain_bounds(self, c_sublist):
		"""
		It's a simple arc-consistency. In this function, we check domains of variables in one row
		and remove impossible values. By this function, domains of one row's vars become almost independent and
		we are sure each var has at least one value
		:param c_sublist: list of one row or column's consistencies
		:return: False if one domain become empty in middle of fix
		"""
		if len(c_sublist) > 1:
			for check_v in range(len(c_sublist) - 1):
				if not c_sublist[check_v].domain:
					return False
				# num colored + one x that can't colored = c[i].num
				down_bound = min(c_sublist[check_v].domain) + c_sublist[check_v].num
				c_sublist[check_v + 1].fix_down_bound(down_bound)

			for check_v in range(len(c_sublist) - 1, 0, -1):
				if not c_sublist[check_v].domain:
					return False
				# num i-1 colored + one x for i that can't be colored = c[i-1].num
				up_bound = max(c_sublist[check_v].domain) - c_sublist[check_v - 1].num
				c_sublist[check_v - 1].fix_up_bound(up_bound)

		return True


class Var:
	def __init__(self, num, depth_no, size):
		"""
		CSP Variables.
		:param num: number of cells should be color
		:param depth_no: number of row or col of var
		:param size: size of board (CSP problem)
		"""
		self.num = num
		self.val = -1
		self.depth_no = depth_no
		self.domain = [i for i in range(size - num + 1)]

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
	"""
	recursive backtracking algorithm
	:param b_csp: csp problem
	:param no_selected: number of variables which have value
	:return: If problem solved or failed
	"""
	if no_selected == b_csp.no_vars:
		if check_col_consistency(b_csp):
			return b_csp
		else:
			return False

	var = var_generator.get_var(no_selected)
	# lcv(b_csp, var)
	my_heuristic(b_csp, var)

	for value in var.domain:
		var.val = value
		var.domain = [value]

		result_of_forwarding, forward_j = forward_checking(b_csp, var, value)
		if not result_of_forwarding:
			reverse_backtrack_step(b_csp, forward_j, var)
			continue

		result = backtrack_rec(b_csp, no_selected + 1)
		if result:
			return result
		reverse_backtrack_step(b_csp, forward_j, var)
	return False


def forward_checking(b_csp, var, value):
	"""
	In this function we color board cells and forward consistency to other variables
	and we check if there was a var with empty domain, reverse changes and go to next value
	:param b_csp: CSP problem
	:param var: Selected variable
	:param value: Selected value
	:return: True if there was no consistency. j is leftest board's cell which affected by this var
	"""
	# coloring and crossing board (in var row)
	if value + var.num < b_csp.size:
		b_csp.board[var.depth_no][value + var.num] = -1

	if var is b_csp.row_cons[var.depth_no][-1]:
		j = value + var.num + 1
		while j < b_csp.size and b_csp.board[var.depth_no][j] == 0:
			b_csp.board[var.depth_no][j] = -1
			j += 1
	j = value - 1
	while j >= 0 and b_csp.board[var.depth_no][j] == 0:
		b_csp.board[var.depth_no][j] = -1
		j -= 1
	for v in range(value, value + var.num):
		b_csp.board[var.depth_no][v] = 1

	# check consistencies
	b_csp.node_consistency()

	# check if row colored well when var is last variable in that row
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
		# TODO: check for cols too
		if not (y == b_csp.size and cons == len(b_csp.row_cons[var.depth_no]) - 1
		        and (colored == 0 or colored == b_csp.row_cons[var.depth_no][cons].num)):
			return False, j

	# check domain's size and if there was an empty one, return False,
	j_check = 0
	while j_check < b_csp.size:
		c = 0
		while c < len(b_csp.col_cons[j_check]) and b_csp.col_cons[j_check][c].domain:
			c += 1
		if c != len(b_csp.col_cons[j_check]):
			break
		j_check += 1
	if j_check != b_csp.size:
		return False, j

	i_check = 0
	while i_check < b_csp.size:
		c = 0
		while c < len(b_csp.row_cons[i_check]) and b_csp.row_cons[i_check][c].domain:
			c += 1
		if c != len(b_csp.row_cons[i_check]):
			break
		i_check += 1
	if i_check != b_csp.size:
		return False, j
	return True, j


def lcv(b_csp, var):
	var_limit_list = np.empty(len(var.domain), dtype=int)
	index = 0
	cpy_domain = var.domain[:]
	for val in cpy_domain:
		result_of_forwarding, forward_j = forward_checking(b_csp, var, val)
		if not result_of_forwarding:
			var_limit_list[index] = 0
			index += 1
			reverse_backtrack_step(b_csp, forward_j, var)
			continue
		s = 0
		for c_sublist in b_csp.col_cons:
			for constraint in c_sublist:
				# if val <= constraint.depth_no < val + var.num:
				# 	s += len(constraint.domain) * constraint.num
				# else:
				s += len(constraint.domain)

		var_limit_list[index] = s
		reverse_backtrack_step(b_csp, forward_j, var)
		index += 1

	order = np.argsort(var_limit_list)[::-1]
	var.domain = [cpy_domain[i] for i in order]


def my_heuristic(b_csp, var):
	var_limit_list = np.empty(len(var.domain), dtype=int)
	index = 0
	cpy_domain = var.domain[:]
	for val in cpy_domain:
		s = 0
		for j in range(val, val + var.num):
			for constraint in b_csp.col_cons[j]:
				s += constraint.num
		var_limit_list[index] = s
		index += 1

	order = np.argsort(var_limit_list)[::-1]
	var.domain = [cpy_domain[i] for i in order]


def reverse_backtrack_step(b_csp, j, var):
	var.val = -1
	j += 1
	while j < b_csp.size:
		b_csp.board[var.depth_no][j] = 0
		j += 1
	var_row = np.where(var_generator.order == var.depth_no)[0][0]

	for row in var_generator.order[var_row + 1:]:
		for col in range(b_csp.size):
			b_csp.board[row][col] = 0
	for c_sublist in b_csp.col_cons:
		for c in c_sublist:
			c.domain = [i for i in range(b_csp.size - c.num + 1)]
	for c_sublist in b_csp.row_cons:
		for c in c_sublist:
			c.domain = [i for i in range(b_csp.size - c.num + 1)]
	b_csp.node_consistency()


def check_col_consistency(b_csp):
	"""
	check consistency of all columns after valuing last variable
	:param b_csp:
	:return: True if there was no consistency
	"""
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
		"""
		Sort variables according to MRV algorithm
		:param var_list: list of variables
		:param no_vars: number of variables
		"""
		var_sublist_sum = np.empty(len(var_list), dtype=int)
		self.var_list = np.empty(no_vars, dtype=object)
		index = 0
		for var_sublist in var_list:
			var_sublist_sum[index] = self.var_sum(var_sublist)
			index += 1
		self.order = np.argsort(var_sublist_sum)[::-1]
		tmp_var_list = var_list[self.order]
		self.idx = 0
		for sub_list in tmp_var_list:
			for e in sub_list:
				self.var_list[self.idx] = e
				self.idx += 1
		self.idx = 0

	def var_sum(self, var_sublist):
		s = 0
		for var in var_sublist:
			s += var.num + 1
		return s - 1

	def get_next_var(self):
		next_var = self.var_list[self.idx]
		self.idx += 1
		return next_var

	def get_var(self, idx):
		return self.var_list[idx]


if __name__ == '__main__':
	# input
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

	# algorithm
	var_generator = VarGenerator(csp.row_cons, csp.no_vars)
	print("Solving")
	start_time = time.time()

	# solving and printing result
	csp.node_consistency()
	if backtrack(csp):
		print()
		print("--- %s seconds ---" % (time.time() - start_time))
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
