```bash
git clone --recursive https://github.com/ndreuu/SMTLIB2.git
git submodule update --init --recursive 
cd ./z3
python3 ./scripts/mk_make.py --dotnet 
cd build; make
cd ../../
dotnet build
```