import os
import sys
import shutil

mono = [
    "perm",
    "bagperm",
    "binom",
    "redblack",
    "trie"
]

folder = "/Users/anabrendel/Desktop/lfind-compat-benchmarks/atomic_vfa"

def write(file,content):
    f = open(file, "w")
    f.write(content)
    f.close()

def coq_makefile(suite,suite_folder,test):
    test_folders = os.path.join(suite_folder,"tests")
    test_name = test.removesuffix(".v")
    test_dir = os.path.join(test_folders,test_name)
    content = f"-R . vfa_{suite}_{test_name}\n\n{test}"
    os.system(f"mkdir {test_dir}")
    coq_project = os.path.join(test_dir,"_CoqProject")
    os.system(f"touch {coq_project}")
    write(coq_project,content)
    return test_dir

def set_up():
    for suite in mono:
        suite_folder = os.path.join(folder,suite)
        for test in os.listdir(suite_folder):
            if test.endswith(".v"):
                test_dir = coq_makefile(suite,suite_folder,test)
                src = os.path.join(suite_folder,test)
                dst = os.path.join(test_dir,test)
                shutil.copy(src,dst)

def make_makefiles():
    for suite in mono:
        suite_folder = os.path.join(folder,suite)
        test_folders = os.path.join(suite_folder,"tests")
        for test in os.listdir(test_folders):
            full_test = os.path.join(test_folders,test)
            os.system(f"cd {full_test} && coq_makefile -f _CoqProject -o Makefile")

def make_monos():
    for suite in mono:
        suite_folder = os.path.join(folder,suite)
        test_folders = os.path.join(suite_folder,"tests")
        for test in os.listdir(test_folders):
            full_test = os.path.join(test_folders,test)
            os.system(f"cd {full_test} && make")