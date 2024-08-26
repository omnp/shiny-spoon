import re

def parse_dimacs(text):
	variables = set()
	clauses = set()
	m = 0
	i = 0
	for line in text.split('\n'):
		line = line.strip()
		if line:
			if line[0] == 'c':
				print(line)
				continue
			elif line[0] == 'p':
				print(line)
				items = re.split('\\s+', line)
				m = int(items[3].strip())
			else:
				items = [int(x.strip()) for x in re.split('\\s+', line)]
				clause = tuple(items[:-1])
				if items[-1] != 0:
					raise ValueError("dimacs ParseError: unexpected token")
				else:
					clauses.add(clause)
					variables = set.union(variables, set(abs(x) for x in clause))
					i += 1
	if i != m:
		raise ValueError("dimacs ParseError: unexpected number of clauses")
	return variables, clauses
