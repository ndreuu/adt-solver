import re

f = open("./output.txt", "r")
content = f.readlines()
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