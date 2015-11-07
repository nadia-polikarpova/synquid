import sys
import os, os.path
import shutil
import time
import pickle
import re
from subprocess import call, check_output
from colorama import init, Fore, Back, Style

# Parameters
SYNQUID_PATH = '..\\src\\Synquid.exe'
BENCH_PATH = '.'
LOGFILE_NAME = 'run_all.log'
OUTFILE_NAME = 'run_all.csv'

BENCHMARKS = [
    ('Int-Max2', []),
    ('Int-Max3', []),
    ('Int-Max4', []),
    ('Int-Max5', []),
    ('Int-Add', []),
]

class SynthesisResult:
    def __init__(self, name, time):
        self.name = name
        self.time = time
        
    def str(self):
        return self.name + ', ' + '{0:0.2f}'.format(self.time) + ', '

def run_benchmark(name, opts):
    print name,

    with open(LOGFILE_NAME, 'a') as logfile:
      start = time.clock()
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

if __name__ == '__main__':
    init()
    results = {}
    
    if os.path.isfile(LOGFILE_NAME):
      os.remove(LOGFILE_NAME)    
    
    for (name, args) in BENCHMARKS:
        run_benchmark(name, args)
    
    postprocess()
  
