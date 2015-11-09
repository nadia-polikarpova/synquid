import sys
import os, os.path
import shutil
import time
import difflib
# import pickle
# import re
from subprocess import call, check_output
from colorama import init, Fore, Back, Style

# Parameters
SYNQUID_PATH = '..\\src\\Synquid.exe'
BENCH_PATH = '.'
LOGFILE_NAME = 'run_all.log'
ORACLE_NAME = 'oracle'
OUTFILE_NAME = 'run_all.csv'

BENCHMARKS = [
    # Integers
    ('Int-Max2', []),
    ('Int-Max3', []),
    ('Int-Max4', []),
    ('Int-Max5', []),
    ('Int-Add', []),
    # Lists
    ('List-Null', []),
    ('List-Elem', []),
    ('List-Stutter', []),
    ('List-Replicate', []),
    ('List-Append', []),
    ('List-Take', []),
    ('List-Drop', []),
    ('List-Delete', []),
    ('List-ToNat', []),    
    # Trees
    ('Tree-Elem', []),
    ('Tree-Flatten', []),    
    # Insertion Sort
    ('IncList-Insert', []),
    ('IncList-InsertSort', []),    
    # Merge sort
    ('List-Split', ['-s=1', '-m=3']),
    ('IncList-Merge', ['-m=2']),
    ('IncList-MergeSort', ['-a=2', '-s=1', '-m=3', '-k']),
    # Quick sort
    ('List-Partition', ['-s=1', '-m=2']),
    ('IncList-PivotAppend', []),
    ('IncList-QuickSort', ['-a=2', '-s=1', '-m=2']),    
]

class SynthesisResult:
    def __init__(self, name, time):
        self.name = name
        self.time = time
        
    def str(self):
        return self.name + ', ' + '{0:0.2f}'.format(self.time) + ', '

def run_benchmark(name, opts):
    print name,

    with open(LOGFILE_NAME, 'a+') as logfile:
      start = time.clock()
      logfile.seek(0, os.SEEK_END)
      return_code = call([SYNQUID_PATH] + opts + [name + '.sq'], stdout=logfile, stderr=logfile)
      end = time.clock()
      
    print '{0:0.2f}'.format(end - start),
    if return_code:        
        print Back.RED + Fore.RED + Style.BRIGHT + 'FAIL' + Style.RESET_ALL
    else:
        results [name] = SynthesisResult(name, (end - start))
        print Back.GREEN + Fore.GREEN + Style.BRIGHT + 'OK' + Style.RESET_ALL
            
def postprocess():
    with open(OUTFILE_NAME, 'w') as outfile:
        for (name, args) in BENCHMARKS:
            outfile.write (name + ',')
            if name in results:
                res = results [name]
                outfile.write ('{0:0.2f}'.format(res.time))
                outfile.write (',')
            outfile.write ('\n')
            
    if os.path.isfile(ORACLE_NAME):
        fromlines = open(ORACLE_NAME).readlines()
        tolines = open(LOGFILE_NAME, 'U').readlines()
        diff = difflib.unified_diff(fromlines, tolines, n=0)
        print
        sys.stdout.writelines(diff)

if __name__ == '__main__':
    init()
    results = {}
    
    if os.path.isfile(LOGFILE_NAME):
      os.remove(LOGFILE_NAME)    
    
    for (name, args) in BENCHMARKS:
        run_benchmark(name, args)
    
    postprocess()
  
