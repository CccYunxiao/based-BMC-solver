# based-BMC-solver
small demo with respect of static program verification based on llvm, BMC, MathSAT solver.

install:

1.llvm version 3.8.0

2.sudo apt-get install cmake bison flex libboost-all-dev python perl minisat libgmp-dev

3.MathSAT 5 smt solver

4.download this project

```bash
compile this project:

mkdir build

cd build

cmake ..

make

./llvmtest ../gcd_1_true-unreach-call_true-no-overflow2reg.ll
```
