#!/usr/bin/env python3

import sys
import csv
from itertools import takewhile, dropwhile, chain, tee, filterfalse, product
import random
from collections import Counter
from os.path import basename

def triangular(n):
	'calculates 1 + 2 + 3 + ... + n in constant time'
	return n*(n+1)/2

def triangular_prime(n, base=10):
	'calculates base-1 + base-2 + base-3 + ... + n in constant time'
	return n*base - triangular(n)

def partition(pred, iterable):
    'Use a predicate to partition entries into false entries and true entries'
    # partition(is_odd, range(10)) --> 0 2 4 6 8   and  1 3 5 7 9
    t1, t2 = tee(iterable)
    return filterfalse(pred, t1), filter(pred, t2)

# lookup table for number-in-cells combinations
# where keys are (number,cell) pairs and values are the only possible set of summands
lookup = {
	(i, 1): {i} for i in range(1,10)
}

for i in range(2,10):
	ti = int(triangular(i))
	invti = int(triangular_prime(i))
	minset = {*range(1,i+1)}
	maxset = {*range(10-i, 10)}

	# complete the lookup table with the smallest possible sum set
	lookup[(ti, i)] = minset
	# ditto for the biggest possible sum set
	lookup[(invti, i)] = maxset
	if i < 9:
		# corollary: if the summands for the smallest and biggest possible sums are unique
		# then the summands for the second biggest/smallest sums are unique as well.
		lookup[(ti+1, i)] = minset ^ {i, i+1} # remove i, add i+1
		lookup[(invti-1, i)] = maxset ^ {10-i, 10-i-1} # remove 10-i, add 10-i-1

class Cell:
	'class for representing a cell with a set of possible values (candidates)'
	def __init__(self, candidates=None):
		self.candidates = set(range(1,10)) if candidates is None else set(candidates)
	def is_unique(self):
		return len(self.candidates) == 1
	def unique_value(self):
		assert self.is_unique()
		return next(iter(self.candidates))
	def substract(self, substract_set):
		old_len = len(self.candidates)
		self.candidates -= substract_set
		return old_len != len(self.candidates)
	def intersect(self, intersect_set):
		old_len = len(self.candidates)
		self.candidates &= intersect_set
		return old_len != len(self.candidates)
	@classmethod
	def contiguous(cls, iterable):
		return takewhile(lambda i: isinstance(i, cls), iterable)
	def __contains__(self, thing):
		return thing in self.candidates
	def __iter__(self):
		return iter(self.candidates)
	def __str__(self):
		if len(self.candidates) >= 5:
			return '%d..%d' % (min(self.candidates),max(self.candidates))
		elif len(self.candidates) >= 1:
			return ''.join(str(i) for i in self.candidates)
		else:
			return '?'

class Clue:
	'Class for representing a clue with horizontal and/or vertical values'
	def __init__(self, vertical=0, horizontal=0):
		self.vertical = vertical
		self.horizontal = horizontal
	def __iter__(self):
		yield self.vertical
		yield self.horizontal
	def __str__(self):
		return str(self.vertical if self.vertical != 0 else '') + '\\' + str(self.horizontal if self.horizontal != 0 else '')

def constrain_cells_sum(n, cells):
	'discards candidates in cells that cannot possibly add to n together'
	count = len(cells)
	assert n >= triangular(count) and n <= triangular_prime(count)
	changed = False
	try:
		# if there is a unique combination, intersect cell candidates with the
		# unique set of summands
		summands = lookup[(n, count)]
		for cell in cells:
			changed = cell.intersect(summands) or changed
	except KeyError:
		pass
	cellset_max = int(min(n-triangular(count-1), 9) if count > 1 else n)
	cellset_min = int(max(n-triangular_prime(count-1), 1) if count > 1 else n)
	for cell in cells:
		# try to discard candidates outside the possible range
		allowed_range = {*range(cellset_min, cellset_max+1)}
		changed = cell.intersect(allowed_range) or changed
	return changed

def valid_combination(iterable):
	iterable = tuple(iterable)
	return len(iterable)==len(set(iterable)) and all(x >= 1 and x <= 9 for x in iterable)

class Map:
	def __init__(self, width, height, data):
		self.width = width
		self.height = height
		self.data = tuple(data)

	def __contains__(self, what):
		return what in self.data

	def get(self, row, column):
		assert row < self.height and column < self.width
		return self.data[row*self.width + column]

	def idx2row(self, idx):
		assert idx < self.width * self.height
		return idx // self.width
	def idx2col(self, idx):
		assert idx < self.width * self.height
		return idx % self.width

	def items_south_of(self, row, column, pred=lambda x: True):
		assert row < self.height and column < self.width
		return self.data[(row+1)*self.width+column::self.width]
	def items_north_of(self, row, column, pred=lambda x: True):
		assert row < self.height and column < self.width
		return self.data[(row-1)*self.width+column:0:-self.width]
	def items_west_of(self, row, column, pred=lambda x: True):
		assert row < self.height and column < self.width
		return self.data[row*self.width+column-1:row*self.width-1:-1]
	def items_east_of(self, row, column, pred=lambda x: True):
		assert row < self.height and column < self.width
		return self.data[row*self.width+column+1:(row+1)*self.width:1]

	def __str__(self):
		return '\n'.join(
			'\t'.join(str(e) for e in self.data[i*self.width:(i+1)*self.width])
			for i in range(self.height)
		)

class Kakuro(Map):
	def __init__(self, *args):
		super(Kakuro, self).__init__(*args)

	@classmethod
	def read_csv(cls, filename):
		with open(filename, 'r') as csvfile:
			reader = csv.reader(csvfile, delimiter=',', quotechar='"')
			row = next(reader)
			width = len(row)
			height = 1
			data = row
			for row in reader:
				assert len(row) == width, 'Wrong row length at line %d' % reader.line_num
				data.extend(row)
				height = height+1
			def deserializeElement(element):
				element = element.strip()
				if '\\' in element:
					vtoken, htoken = element.split('\\')
					vtoken = vtoken.strip()
					htoken = htoken.strip()
					return Clue(int(vtoken or 0), int(htoken or 0))
				else:
					if element != '' and element != '0':
						return Cell(set(map(int,element)))
					else:
						return Cell()
			return Kakuro(width, height, tuple(map(deserializeElement, data)))
		return None

	def is_solved(self):
		for element in self.data:
			if type(element) == Cell:
				if not element.is_unique():
					return False
		for row, column, clue in self.clues():
			vneighbors = tuple(c.unique_value() for c in Cell.contiguous(self.items_south_of(row, column)))
			hneighbors = tuple(c.unique_value() for c in Cell.contiguous(self.items_east_of(row, column)))
			if len(hneighbors) != len(set(hneighbors)) or len(vneighbors) != len(set(vneighbors)):
				return False
			if clue.vertical != sum(vneighbors) or clue.horizontal != sum(hneighbors):
				return False
		return True

	def clues_for(self, row, column):
		'Get a pair (vertical_clue, horizontal_clue) from the two clues for a cell'
		predicate = lambda c: not isinstance(c, Clue)
		items_v = dropwhile(predicate, self.items_north_of(row, column))
		items_h = dropwhile(predicate, self.items_west_of(row, column))
		return (next(items_v), next(items_h))

	def discard_from_uniques(self):
		'Examines cells with unique candidates to discard from neighboring cells (cheapest)'
		changed = False
		for row, column, clue in self.clues():
			vcells = self.items_south_of(row, column)
			hcells = self.items_east_of(row, column)
			for n, cells in zip(clue, (vcells, hcells)):
				if n == 0:
					continue
				pending, uniques = partition(Cell.is_unique, Cell.contiguous(cells))
				pending = tuple(pending)
				uniques = tuple(uniques)

				substract_set = {u.unique_value() for u in uniques}
				assert len(substract_set) == len(uniques)
				for p in pending:
					changed = p.substract(substract_set) or changed
				n -= sum(substract_set)
				if n != 0:
					changed = constrain_cells_sum(n, pending) or changed
		return changed

	def discard_from_single_clues(self):
		'''Examines clues with pending cells and discards
		infeasible candidates (expensive).
		Returns true if new information was found'''
		changed = False
		for row, column, clue in self.clues():
			vstrip = Cell.contiguous(self.items_south_of(row, column))
			hstrip = Cell.contiguous(self.items_east_of(row, column))
			for n, strip in zip(clue, (vstrip, hstrip)):
				if n == 0:
					continue
				pending, uniques = partition(Cell.is_unique, strip)
				pending = set(pending)
				n -= sum(u.unique_value() for u in uniques)
				assert len(pending) > 0 and n > 0 or len(pending) == 0 and n == 0
				if n == 0:
					continue
				for cell in pending:
					neighbors = pending - {cell}
					changed = cell.substract({
						x for x in cell
						if not any(
							n == sum(p)+x for p in product(*neighbors)
							if valid_combination((x,*p))
						)
					}) or changed
		return changed

	def crack(self):
		'Finds a solution using brute force. (most expensive)'
		pending_cells = tuple(cell for row, col, cell in self.cells() if not cell.is_unique())
		candidates = tuple(c.candidates for c in pending_cells)
		cartesian = product(*candidates)
		solutions = []
		for combination in cartesian:
			for x, cell in zip(combination, pending_cells):
				cell.candidates = {x}
			if self.is_solved():
				solutions += [combination]
				#return True
		if len(solutions) == 0:
			return False
		for x, cell in zip(solutions[0], pending_cells):
			cell.candidates = {x}
		print('solutions: {}'.format(len(solutions)))
		return True

	def clues(self):
		'Get an iterable of (row, column, clue) for the clues in the grid'
		return ((self.idx2row(idx), self.idx2col(idx), item) for idx,item in enumerate(self.data) if isinstance(item, Clue))
	def cells(self):
		'Get an iterable of (row, column, cell) for the cells in the grid'
		return ((self.idx2row(idx), self.idx2col(idx), item) for idx,item in enumerate(self.data) if isinstance(item, Cell))

	def solve(self):
		changed = True
		while changed:
			changed = self.discard_from_uniques()
			if not changed:
				changed = self.discard_from_single_clues()
		self.crack()

def usage():
	print('Usage: %s %s FILE' % (basename(sys.executable), sys.argv[0]))

if __name__ == '__main__':
	if len(sys.argv) != 2:
		usage()
		sys.exit(1)

	kakuro = Kakuro.read_csv(sys.argv[1])
	kakuro.solve()
	print(str(kakuro))
	print('Success.' if kakuro.is_solved() else 'Failure!')
