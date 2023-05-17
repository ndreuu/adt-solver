```bash
git clone --recursive https://github.com/ndreuu/SMTLIB2.git
cd ./z3
python3 ./scripts/mk_make.py --dotnet 
cd build; make
cd ../../
dotnet build 
```


For debug trace use
```bash
python dbg.py <dbg_folder>
```
