import itertools
def main():
	v = list([1,2,3])
	b = list(v)
	b.pop(0)
	print(v)
	print(b)
	g = list()
	g.append(2)
	for i in range(3):
		for j in range(3):
			for x in range(j+1, 3):
				print(i,j,i,x)

	
	for i in itertools.product(*[[1,2],[1,2,3]]):
		print(i)

	r = list([1,2,3])
	print(r)
main()