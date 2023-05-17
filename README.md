```bash
git clone --recursive https://github.com/ndreuu/SMTLIB2.git
git submodule update --init --recursive 
git clone https://github.com/ndreuu/z3.git
cd ./z3
git checkout 4.11.2
python3 ./scripts/mk_make.py --dotnet 
cd build; make
cd ../../
dotnet build 
```
    