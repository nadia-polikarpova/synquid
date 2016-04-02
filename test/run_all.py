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
COMMON_OPTS = []
TIMEOUT_COMMAND = 'timeout'
TIMEOUT= '120'

BENCHMARKS = [
    # Integers
    ('Int-Max2',    []),
    ('Int-Max3',    []),
    ('Int-Max4',    []),
    ('Int-Max5',    []),
    ('Int-Add',     []),
    # Lists
    ('List-Null',       []),
    ('List-Elem',       []),
    ('List-Stutter',    []),
    ('List-Replicate',  []),
    ('List-Append',     ['-m=1']),
    ('List-Concat',     []),
    ('List-Take',       []),
    ('List-Drop',       []),
    ('List-Delete',     []),
    ('List-Map',        []),
    ('List-ZipWith',    []),
    ('List-Zip',        []),
    ('List-ToNat',      []),
    ('List-Product',    []),
    ('List-ExtractMin',     ['-a=2', '-m 3']),
    ('List-Fold',           []),
    ('List-Fold-Length',    ['-m=0']),
    ('List-Fold-Append',    ['-m=0']),
    ('List-Snoc',           []),
    ('List-Reverse',        []),
    # Unique lists
    ('UniqueList-Insert',   []),
    ('UniqueList-Delete',   []),
    ('List-Nub',            ['-f=FirstArgument', '-m=1', '-g']),
    ('List-Compress',       []),
    # Insertion sort
    ('List-InsertSort',     []),
    ('List-Fold-Sort',      ['-m=1', '-a=2', '-e']),
    # Merge sort
    ('List-Split',          ['-m=3']),
    ('IncList-Merge',       []),
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
    ('BST-Delete',          ['-e']),
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
]

AVL_BENCHMARKS = [
    # AVL trees
    ('AVL-BalL0',           ['-a 2']),
    ('AVL-BalLL',           ['-a 2', '-u']),
    ('AVL-BalLR',           ['-a 2', '-u']),
    ('AVL-BalR0',           ['-a 2']),
    ('AVL-BalRL',           ['-a 2', '-u']),
    ('AVL-BalRR',           ['-a 2', '-u']),
    ('AVL-BalanceL',        ['-a 2', '-e']),
    ('AVL-BalanceR',        ['-a 2', '-e']),
    ('AVL-Insert',          ['-a 2']),
]

RBT_BENCHMARKS = [
    # Red-black trees
    ('RBT-BalanceL',        ['-a 2', '-m 1', '-z']),
    ('RBT-BalanceR',        ['-a 2', '-m 1', '-z']),
    ('RBT-Insert',          ['-a 2', '-m 1', '-z']),
]

CHECKING_BENCHMARKS = [
    ('List-Append',         []),
    ('List-Replicate',      []),
    ('List-ToNat',          []),
    ('AVL',                 []),
]

class SynthesisResult:
    def __init__(self, name, time):
        self.name = name
        self.time = time

    def str(self):
        return self.name + ', ' + '{0:0.2f}'.format(self.time) + ', '

def run_benchmark(name, opts, path='.'):
    global total_time
    print name,

    with open(LOGFILE_NAME, 'a+') as logfile:          
      start = time.time()
      logfile.seek(0, os.SEEK_END)
      return_code = call([synquid_path] + COMMON_OPTS + opts + [os.path.join (path, name + '.sq')], stdout=logfile, stderr=logfile)
      end = time.time()

      t = end - start
      print '{0:0.2f}'.format(t),
      total_time = total_time + t
      if return_code:
          print Back.RED + Fore.RED + Style.BRIGHT + 'FAIL' + Style.RESET_ALL
      else:
          results [name] = SynthesisResult(name, t)
          print Back.GREEN + Fore.GREEN + Style.BRIGHT + 'OK' + Style.RESET_ALL
          
def run_test(name, path='.'):
    print name

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

def show_diff():            
    if os.path.isfile(ORACLE_NAME):
        fromlines = open(ORACLE_NAME).readlines()
        tolines = open(LOGFILE_NAME, 'U').readlines()
        diff = difflib.unified_diff(fromlines, tolines, n=0)
        print
        sys.stdout.writelines(diff)

if __name__ == '__main__':
    init()
    results = {}
    total_time = 0

    if platform.system() == 'Linux':
        synquid_path = SYNQUID_PATH_LINUX
    else:
        synquid_path = SYNQUID_PATH_WINDOWS
        
    if len(sys.argv) == 1:
        # Default: run synthesis benchmarks in 'current' directory, which must succeed; compare results with oracle
        os.chdir('current')
        if os.path.isfile(LOGFILE_NAME):
            os.remove(LOGFILE_NAME)
            
        for (name, args) in BENCHMARKS:
            run_benchmark(name, args)
            
        for (name, args) in RBT_BENCHMARKS:
            run_benchmark(name, args, 'RBT')

        for (name, args) in AVL_BENCHMARKS:
            run_benchmark(name, args, 'AVL')
            
        print 'TOTAL', '{0:0.2f}'.format(total_time)
            
        write_times(BENCHMARKS + RBT_BENCHMARKS + AVL_BENCHMARKS)
        show_diff()
        
    elif sys.argv[1] == 'unit':
        # Run unit tests 
        os.chdir('unit')
        if os.path.isfile(LOGFILE_NAME):
            os.remove(LOGFILE_NAME)        
        
        for name in os.listdir('.'):
            filename, file_extension = os.path.splitext(name)
            if file_extension == '.sq':
                run_test(filename)
        
        show_diff()
    
    else:
        print 'Unknown command-line argument', sys.argv[1]