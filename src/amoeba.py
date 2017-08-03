import argparse
import sys, os

from argparse import RawTextHelpFormatter
from argparse import ArgumentParser


# keep the imtermediate binary/final.s or not.
k = False
f_dic = ""

iter_num = 0

def check_32():
    lines = []
    with open("elf.info") as f:
        lines = f.readlines()
    if "32-bit" in lines[0]:
        return True
    else:
        return False

def check_strip():
    lines = []
    with open("elf.info") as f:
        lines = f.readlines()
    if "not stripped" in lines[0]:
        return True
    else:
        return False


if __name__ == "__main__":
    p = ArgumentParser(formatter_class=RawTextHelpFormatter)
    p.add_argument("binary",
                   help="path to the input binary, for example, /home/szw175/ls")
    p.add_argument("-i", "--iteration", type=int,
                   help="the number of disassemble-(instrument)-reassemble iterations")

    args = p.parse_args()
    b = args.binary
    i = args.iteration
    iter_num = i

    os.system('file ' + b + ' > elf.info')

    if check_strip() == False or check_32() == False:
        print "error input"

    else:
        if args.iteration:
            os.system("python uroboros.py " + b + " -i " + str(i) + " -k")
        else:
            print "user must specify the number of iterations"
