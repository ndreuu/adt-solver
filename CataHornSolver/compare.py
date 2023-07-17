def nonEmpty(xs):
    return list(filter(lambda x: x.__contains__(".smt2"), xs))

cata = open("output.csv", "r")
cata = nonEmpty(cata.readlines())
spacer = open("spacer.csv", "r")
spacer = nonEmpty(spacer.readlines())
eldarica = open("eldarica.csv", "r")
eldarica = nonEmpty(eldarica.readlines())

def split(xs):
    return list(map(lambda x: x.split(","), xs))

def compare(contentName: str, content: str, otherName: str, other: str):
    _content = list(map(lambda x: x if x[1].__contains__("SAT") or x[1].__contains__("UNKNOWN") else ([ x[0], "-"]), split(content)))
    _other = list(map(lambda x: x if x[1].__contains__("SAT") or x[1].__contains__("UNKNOWN") else ([ x[0].__str__(), "-"]), split(other) ))

    _content.sort(key=lambda x: x[0])
    _other.sort(key=lambda x: x[0])

    xs = list(zip((_content), (_other)))

    for ([name, cataRes], [_, otherRes]) in xs:
        if (cataRes.__contains__("UNSAT") and (not otherRes.__contains__("UNSAT") and otherRes.__contains__("SAT"))):
            print(name + "\n" + contentName + cataRes + otherName + ":" + otherRes)
        elif (cataRes.__contains__("SAT") and (not otherRes.__contains__("SAT") and otherRes.__contains__("UNSAT"))):
            print(name + "\n" + contentName + cataRes + otherName + ":" + otherRes)


print("Compare with Spacer")
compare("Cata", cata, "Spacer", spacer)

print("Compare with Eldarica")
compare("Cata", cata, "Eldarica", eldarica)



