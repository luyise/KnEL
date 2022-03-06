build:
	@dune build

test: build
	@./src/main.exe ./tests/test1.knl
	@./src/main.exe ./tests/topology.knl

clean:
	dune clean
