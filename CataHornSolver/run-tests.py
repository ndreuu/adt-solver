import sys
import subprocess
import tempfile
import os

args = sys.argv[1:] 

def add_unsat_res(unsats_path, file, bench, result):
    f = open((os.path.join(unsats_path, file)), "w")
    f.write(bench + "\n" + result)
    f.close()

def add_sat_res(sat_pah, file, bench, result):
    f = open(os.path.join(sat_pah, file), "w")
    f.write(bench)
    f.close()
    r = open(os.path.join(sat_pah, file) + ".res", "w")
    r.write(result)
    r.close()


def add_in_table(table, name, result):
    r = open(table, "a")
    r.write(name + ", " + result + "\n")
    r.close()




def run(path, file, table, unsats, sats, timeout):
    try:
        tmp = tempfile.TemporaryFile()
        subprocess.run([path, file], stdout=tmp, timeout=timeout)
        
        tmp.seek(0)
        out = tmp.read().decode().split("\n")
        
        if out[0] == "unsat":
            add_in_table(os.path.basename(file), "UNSAT")
            add_unsat_res(table, unsats, os.path.basename(file), open(file, "r").read(), "\n".join(out[2:]))
        elif out[0] == "sat":
            add_in_table(table, os.path.basename(file), "SAT")
            add_sat_res(sats, os.path.basename(file), open(file, "r").read(), "\n".join(out[2:]))
        else:
            add_in_table(table, os.path.basename(file), out[0])
    except subprocess.TimeoutExpired as e:
        add_in_table(table, os.path.basename(file), "TL")




run('./bin/Release/net6.0/CataHornSolver', args[0], "./table.csv", './unsats', './sats', 5)
