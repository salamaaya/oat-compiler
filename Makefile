SUBMIT := $(shell cat submit_zip_contents.txt)
HWNAME := hw10
TIMESTAMP := $(shell /bin/date "+%Y-%m-%d-%H:%M:%S")
ZIPNAME := $(HWNAME)-submit-$(TIMESTAMP).zip

.PHONY: all oatc test clean zip

all: oatc

oatc: 
	dune build bin/main.exe
	@cp bin/main.exe oatc

printanalysis: 
	dune build bin/printanalysis.exe
	@cp bin/printanalysis.exe printanalysis

test: oatc
	./oatc --test

utop:
	dune utop

zip: $(SUBMIT)
	zip '$(ZIPNAME)' $(SUBMIT)

clean:
	dune clean
	rm -rf oatc ocamlbin bin/main.exe printanalysis bin/printanalysis.exe a*.out

# make experiments FILE=foo.oat 
# will create four executables, one for each 
oat_experiments: oatc
	echo "Generating executables for $(FILE) with optimization $(OPT)"
	./oatc -o a_baseline$(OPT).out --liveness trivial --regalloc none $(OPT) $(FILE) bin/runtime.c
	./oatc -o a_greedy$(OPT).out --liveness dataflow --regalloc greedy $(OPT) $(FILE) bin/runtime.c
	./oatc -o a_better$(OPT).out --liveness dataflow --regalloc better $(OPT) $(FILE) bin/runtime.c
	./oatc -o a_clang$(OPT).out --clang $(FILE) $(OPT) bin/runtime.c
	time ./a_baseline$(OPT).out
	time ./a_greedy$(OPT).out
	time ./a_better$(OPT).out
	time ./a_clang$(OPT).out


ll_experiments: oatc
	echo "Generating executables for $(FILE) with optimization $(OPT)"
	./oatc -o a_baseline$(OPT).out --liveness trivial --regalloc none $(OPT) $(FILE) 
	./oatc -o a_greedy$(OPT).out --liveness dataflow --regalloc greedy $(OPT) $(FILE) 
	./oatc -o a_better$(OPT).out --liveness dataflow --regalloc better $(OPT) $(FILE) 
	./oatc -o a_clang$(OPT).out --clang $(FILE) $(OPT) 
	time ./a_baseline$(OPT).out
	time ./a_greedy$(OPT).out
	time ./a_better$(OPT).out
	time ./a_clang$(OPT).out

# 
