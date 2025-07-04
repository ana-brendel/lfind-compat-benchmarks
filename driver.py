import os
import sys

read = lambda x: open(x, "r").read().split("\n")

def write(file,content):
    f = open(file, "w")
    f.write(content)
    f.close()

imports = "Load LFindLoad.\nFrom lfind Require Import LFind.\nUnset Printing Notations.\nSet Printing Implicit."
original_imports = "From LFindToo Require Import LFindToo."

lfind = "lfind."
admitted = "Admitted."

path = os.getcwd()

def flipping(arg):
    add_tactic = arg == "add_tactic"
    for suite in os.listdir(path):
        if not suite.endswith(".py"):
            full_suite = os.path.join(path,suite)
            tests = os.path.join(full_suite,"tests")
            for test in os.listdir(tests):
                full_test = os.path.join(tests,test)
                test_content = read(full_test)
                to_replace = admitted if add_tactic else lfind
                replace_with = (lfind + " " + admitted) if add_tactic else ""
                rp = lambda l: l.replace(to_replace, replace_with)
                updated = list(map(rp,test_content))
                write(full_test,"\n".join(updated))

def make_tests():
    for suite in os.listdir(path):
        if not suite.endswith(".py"):
            full_suite = os.path.join(path,suite)
            tests = os.path.join(full_suite,"tests")
            make_makefile = f"cd {tests} && coq_makefile -f _CoqProject -o Makefile"
            make = f"cd {tests} && make"
            os.system(make_makefile)
            os.system(make)

def make_common():
    for suite in os.listdir(path):
        if not suite.endswith(".py"):
            full_suite = os.path.join(path,suite)
            common = os.path.join(full_suite,"common")
            make_makefile = f"cd {common} && coq_makefile -f _CoqProject -o Makefile"
            make = f"cd {common} && make"
            os.system(make_makefile)
            os.system(make)

if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "make":
        make_tests()
    elif len(sys.argv) > 1 and sys.argv[1] == "make_common":
        make_tests()
    else:
        arg = "" if len(sys.argv) == 1 else sys.argv[1]
        flipping(arg)