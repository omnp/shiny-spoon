def parse_dimacs(text):
	variables = set()
	clauses = set()
	m = 0
	i = 0
	for line in text.split('\n'):
		if line:
			if line[0] == 'c':
				print(line)
				continue
			elif line[0] == 'p':
				print(line)
				items = line.split(' ')
				m = int(items[3])
			else:
				items = [int(x) for x in line.split(' ')]
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

