#!/usr/bin/python
import sys
import os, os.path
import platform
import shutil
import time
import re
import difflib
from subprocess import call, check_output
from colorama import init, Fore, Back, Style

# Parameters
SYNQUID_PATH_LINUX = 'synquid'
SYNQUID_PATH_WINDOWS = 'Synquid.exe'
BENCH_PATH = '.'
LOGFILE_NAME = 'results.log'
ORACLE_NAME = 'oracle'
OUTFILE_NAME = 'results.csv'
COMMON_OPTS = ['-z']
TIMEOUT_COMMAND = 'timeout'
TIMEOUT= '120'

SECTIONS = ['.', 'sygus', 'rbt', 'AVL']

BENCHMARKS = {
  '.' : [
              # Integers
              ('Int-Add',     []),
              # Lists
              ('List-Null',       []),
              ('List-Elem',       []),
              ('List-Stutter',    []),
              ('List-Replicate',  []),
              ('List-Append',     []),
              ('List-Concat',     []),
              ('List-Take',       []),
              ('List-Drop',       []),
              ('List-Delete',     []),
              ('List-Map',        []),
              ('List-ZipWith',    []),
              ('List-Zip',        []),
              ('List-ToNat',      ['-m 0']),
              ('List-Product',    []),
              ('List-ExtractMin',     ['-a=2', '-m 3']),
              ('List-Intersection',   []),
              ('List-Fold',           []),
              ('List-Fold-Length',    ['-m=0']),
              ('List-Fold-Append',    ['-m=0']),
              ('List-Ith',            []),
              ('List-ElemIndex',      []),
              ('List-Snoc',           []),
              ('List-Reverse',        []),
              # ('List-Range',          []),
              # ('List-Filter',         ['-g=False']),
              # Unique lists
              ('UniqueList-Insert',   []),
              ('UniqueList-Delete',   []),
              ('UniqueList-Range',    []),
              ('List-Nub',            []),
              ('List-Compress',       []),
              # Insertion sort
              ('List-InsertSort',     []),
              ('List-Fold-Sort',      ['-m=1', '-a=2', '-e']),
              # Merge sort
              ('List-Split',          ['-m=3']),
              ('IncList-Merge',       ['-f=AllArguments']),
              ('IncList-MergeSort',   ['-a=2', '-m=3']),
              # Quick sort
              ('List-Partition',      []),
              ('IncList-PivotAppend', []),
              ('IncList-QuickSort',   ['-a=2']),
              # Trees
              ('Tree-Elem',           []),
              ('Tree-Flatten',        []),
              # Binary search tree
              ('BST-Member',          []),
              ('BST-Insert',          []),
              ('BST-ExtractMin',      ['-a=2', '-m=3']),
              ('BST-Delete',          []),
              ('BST-Sort',            []),
              # Binary heap
              ('BinHeap-Member',      []),
              ('BinHeap-Insert',      []),
              # User-defined datatypes
              ('Evaluator',           []),
              ('AddressBook-Make',    ['-a=2']),
              ('AddressBook-Merge',   ['-a=2']),
              # Synthesis from examples
              ('Replicate-Examples',  []),
           ],
  'sygus' : [
              ('Int-Max2',    []),
              ('Int-Max3',    []),
              ('Int-Max4',    []),
              ('Int-Max5',    []),
              ('Array-Search-2', []),
              ('Array-Search-3', []),
              ('Array-Search-4', []),
              ('Array-Search-5', []),
              ('Array-Search-6', []),
            ],
  'AVL' : [
              # AVL trees
              ('AVL-BalL0',           ['-a 2']),
              ('AVL-BalLL',           ['-a 2', '-u']),
              ('AVL-BalLR',           ['-a 2', '-u']),
              ('AVL-BalR0',           ['-a 2']),
              ('AVL-BalRL',           ['-a 2', '-u']),
              ('AVL-BalRR',           ['-a 2', '-u']),
              ('AVL-Balance',         ['-a 2', '-e']),
              ('AVL-Insert',          ['-a 2']),
              ('AVL-ExtractMin',      ['-a 2']),
              ('AVL-Delete',          ['-a 2', '-m 1']),
          ],
  'rbt' : [
    # Red-black trees
    ('RBT-BalanceL',        ['-a 2', '-u', '-z']),
    ('RBT-BalanceR',        ['-a 2', '-u', '-z']),
    ('RBT-Insert',          ['-a 2', '-m 1', '-z']),
          ]
}

# RBT_BENCHMARKS = [
    # # Red-black trees
    # ('RBT-BalanceL',        ['-a 2', '-m 1', '-z']),
    # ('RBT-BalanceR',        ['-a 2', '-m 1', '-z']),
    # ('RBT-Insert',          ['-a 2', '-m 1', '-z']),
# ]

CHECKING_BENCHMARKS = [
    ('List-Append-Bad',     []),
    ('List-Replicate',      []),
    ('List-ToNat',          []),
    ('AVL',                 []),
]

DEMO_BENCHMARKS = [
    ('BST-Insert',          []),
    ('Holes',               []),
    ('List-Replicate',      []),
    ('List-Reverse',        []),
    ('NNF',                 []),
    ('Sort-Fold',           ['-m 1', '-a 2', '-e']),
]

UNIT_TESTS = [
    ('Constructors',         []),
    ('Pairs',                []),
    ('HigherOrder',          []),
    ('TypeAbduction',        []),
    ('CheckMeasures',        []),
    ('Instantiation',        []),
    ('MultiArgMeasures',     []),
    ('HOChecking',           []),
    ('Incr',                 []),
]


class SynthesisResult:
    def __init__(self, name, time):
        self.name = name
        self.time = time

    def str(self):
        return self.name + ', ' + '{0:0.2f}'.format(self.time) + ', '

def cmdline():
    import argparse
    a = argparse.ArgumentParser()
    a.add_argument('--synquid', help='synquid command')
    a.add_argument('--unit', action='store_true', help='run unit tests')
    a.add_argument('--check', action='store_true', help='run type checking tests')
    a.add_argument('--synt', action='store_true', help='run synthesis tests')
    a.add_argument('--sections', nargs="*", choices=SECTIONS + ['all'], default=['all'], help=('which synthesis tests to run'))
    a.add_argument('--demo', action='store_true', help='run demo tests')
    return a.parse_args()

def printerr(str):
    print (Back.RED + Fore.RED + Style.BRIGHT + str + Style.RESET_ALL)

def printok(str):
    print (Back.GREEN + Fore.GREEN + Style.BRIGHT + str + Style.RESET_ALL)

def printwarn(str):
    print (Back.YELLOW + Fore.YELLOW + Style.BRIGHT + str + Style.RESET_ALL)

def run_benchmark(name, opts, path='.'):
    global total_time
    print (name),

    with open(LOGFILE_NAME, 'a+') as logfile:
      start = time.time()
      logfile.seek(0, os.SEEK_END)
      return_code = call([synquid_path] + COMMON_OPTS + opts + [os.path.join (path, name + '.sq')], stdout=logfile, stderr=logfile)
      end = time.time()

      t = end - start
      print ('{0:0.2f}'.format(t)),
      total_time = total_time + t
      bad_flag = name.endswith("-Bad")
      if (bool(return_code) ^ bad_flag):
          printerr("FAIL")
      else:
          printok("OK")
          results [name] = SynthesisResult(name, t)


def run_test(name, path='.'):
    print (name)

    with open(LOGFILE_NAME, 'a+') as logfile:
      logfile.seek(0, os.SEEK_END)
      call([synquid_path] + COMMON_OPTS + [os.path.join (path, name + '.sq')], stdout=logfile, stderr=logfile)

def write_times(benchmarks):
    with open(OUTFILE_NAME, 'w') as outfile:
        for (name, args) in benchmarks:
            outfile.write (name + ',')
            if name in results:
                res = results [name]
                outfile.write ('{0:0.2f}'.format(res.time))
                outfile.write (',')
            outfile.write ('\n')

def check_diff ():
    print
    if not os.path.isfile(ORACLE_NAME):
        # Create oracle
        printwarn('Oracle file not found, creating a new one')
        shutil.copyfile(LOGFILE_NAME,ORACLE_NAME)
    else:
        # Compare log with oracle
        fromlines = open(ORACLE_NAME, 'U').readlines()
        tolines = open(LOGFILE_NAME, 'U').readlines()
        diff = difflib.unified_diff(fromlines, tolines, n=0)

        # Check if diff is empty
        try:
            first = next(diff)
            printerr('TESTS FAILED WITH DIFF')
            print
            print(first)
            sys.stdout.writelines(diff)
            print
            return True

        except StopIteration:
            printok('TESTS PASSED')
            print
            return False


if __name__ == '__main__':
    init()
    results = {}
    total_time = 0

    a = cmdline()

    # Determine the synquid command to use:
    if a.synquid:
        synquid_path = a.synquid
    if platform.system() in ['Linux', 'Darwin']:
        synquid_path = SYNQUID_PATH_LINUX
    else:
        synquid_path = SYNQUID_PATH_WINDOWS

    # By default enable all tests:
    if not (a.unit or a.check or a.synt or a.demo):
      a.unit = True
      a.check = True
      a.synt = True

    sections = [s.lower() for s in a.sections]

    fail = False
    if a.unit:
        # Run unit tests
        os.chdir('unit')
        if os.path.isfile(LOGFILE_NAME):
            os.remove(LOGFILE_NAME)

        # for name in os.listdir('.'):
            # filename, file_extension = os.path.splitext(name)
            # if file_extension == '.sq':
                # run_test(filename)
        for (name, args) in UNIT_TESTS:
            run_benchmark(name, args)                
                
        fail = check_diff()
        os.chdir('..')

    if not fail and a.check:
        # Run type checking benchmarks
        os.chdir('checking')
        if os.path.isfile(LOGFILE_NAME):
            os.remove(LOGFILE_NAME)
        for (name, args) in CHECKING_BENCHMARKS:
            run_benchmark(name, args)
        fail = check_diff()
        os.chdir('..')

    if not fail and a.demo:
        # Test online demos
        os.chdir('demo') 
        if os.path.isfile(LOGFILE_NAME):
            os.remove(LOGFILE_NAME)
        for (name, args) in DEMO_BENCHMARKS:
            run_benchmark(name, args)
        fail = check_diff()
        os.chdir('..')

    if not fail and a.synt:
        # Run synthesis benchmarks in 'current' directory
        os.chdir('current')
        if os.path.isfile(LOGFILE_NAME):
            os.remove(LOGFILE_NAME)

        for sec in SECTIONS:
            if sec in sections or 'all' in sections:
                for (name, args) in BENCHMARKS[sec]:
                    run_benchmark(name, args, sec)

        print('TOTAL', '{0:0.2f}'.format(total_time))

        if sections == ['all']:
            write_times(sum(BENCHMARKS.values(), []))
            check_diff()
        os.chdir('..')


