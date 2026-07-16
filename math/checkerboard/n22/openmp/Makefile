CXX ?= g++
CXXFLAGS ?= -O3 -march=native -std=c++20 -Wall -Wextra -Wpedantic -fopenmp

.PHONY: all clean test
all: dmono22_openmp dmono22_augment_openmp

dmono22_openmp: dmono22_openmp.cpp
	$(CXX) $(CXXFLAGS) $< -o $@

dmono22_augment_openmp: dmono22_augment_openmp.cpp
	$(CXX) $(CXXFLAGS) $< -o $@

test: all
	./dmono22_openmp --n 8 --target 12 --threads 2 --trials 20 --steps 20000 --witness smoke_witness.txt --quiet
	python3 verify_witness.py smoke_witness.txt --n 8 --parity 0 --size 12
	python3 verify_witness.py examples/n22_33.txt --n 22 --parity 0 --size 33
	python3 verify_witness.py examples/n22_near34_one_conflict.txt --n 22 --parity 0 --size 34 --expect-collinear-triples 1
	./dmono22_augment_openmp --seed examples/n22_33.txt --destroy 0 --threads 2 --quiet || test $$? -eq 2

clean:
	rm -f dmono22_openmp dmono22_augment_openmp smoke_witness.txt n22_34.txt n22_34.txt.best dmono22_augmented.txt
