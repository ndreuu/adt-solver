import re

f = open("./output.txt", "r")
content = f.readlines()
content = list(filter(lambda x: not x == "/usr/share/dotnet/sdk/6.0.412/Microsoft.Common.CurrentVersion.targets(2302,5): warning MSB3270: There was a mismatch between the processor architecture of the project being built \"MSIL\" and the processor architecture of the reference \"/home/runner/.nuget/packages/microsoft.z3/4.11.2/lib/netstandard2.0/Microsoft.Z3.dll\", \"AMD64\". This mismatch may cause runtime failures. Please consider changing the targeted processor architecture of your project through the Configuration Manager so as to align the processor architectures between your project and references, or take a dependency on references with a processor architecture that matches the targeted processor architecture of your project. [/home/runner/work/adt-solver/adt-solver/CataHornSolver/CataHornSolver.fsproj]\n", content))
fstName = content[0]
lastRes = content[-1]
content = "".join(content)


dirty = re.findall(r"(?:.*\n.*\.smt2\n\(INIT\)SMT\.NIA)|(?:(?:.*\.smt2.*\n)*ERR .*\n.*\.smt2)", content)


mixedWihAnsStrs = list(map(lambda x: x.replace("\n(INIT)SMT.NIA", ""), dirty))


strs = fstName + re.sub(
    r"\.smt2\n.*\.smt2",
    ".smt2",
    "\n".join(mixedWihAnsStrs)) + "\n" + lastRes


tableContent = re.sub(
    r"\.smt2\n",
    ".smt2 ",
    strs)



normilizedTableContent = re.sub(
    r".smt2 [0-9]+",
    ".smt2 TL",
    tableContent)



table = re.sub(
    r".smt2 ",
    ".smt2, ",
    normilizedTableContent)

table = re.sub(
    r"ERR ",
    "ERR-",
    table)


print(table)
