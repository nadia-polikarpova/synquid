import sys
import os, os.path
import platform
import shutil
import time
import re
import difflib
from subprocess import call, check_output, STDOUT
from colorama import init, Fore, Back, Style

# Globals
SYNQUID_CMD = 'synquid'                                         # Command to call Synquid
LOGFILE_NAME = 'run_small.log'                                  # Log file
ORACLE_NAME = 'solutions_small'                                 # Solutions file
COMMON_OPTS = ['--print-solution-size', '--print-spec-size']    # Options to use for all benchmarks

class Benchmark:
    def __init__(self, name, description, components='', options=[]):
        self.name = name                # Id
        self.description = description  # Description (in the table)
        self.components = components    # Description of components used (in the table)
        self.options = options          # Command-line options to use for this benchmark when running in individual context

    def str(self):
        return self.name + ': ' + self.description + ' ' + str(self.options)

class BenchmarkGroup:
    def __init__(self, name, default_options, benchmarks):
        self.name = name                        # Id
        self.default_options = default_options  # Command-line options to use for all benchmarks in this group when running in common context
        self.benchmarks = benchmarks            # List of benchmarks in this group

ALL_BENCHMARKS = [
    BenchmarkGroup('Integer', [], [
        Benchmark('Int-Max2', 'maximum of 2'),
        Benchmark('Int-Max3', 'maximum of 3'),
        ]),
    BenchmarkGroup("List", [], [
        Benchmark('List-Null', 'is empty', 'true, false'),
        Benchmark('List-Elem', 'is member', 'true, false'),
        Benchmark('List-Stutter', 'duplicate each element'),
        Benchmark('List-Replicate', '$n$ copies of value', '0, inc, dec'),
        Benchmark('List-Append', 'append two lists', '', ['-m=1']),
        Benchmark('List-Concat', 'concatenate list of lists', 'append'),
        Benchmark('List-Take', 'take first $n$ elements', '0, inc, dec'),
        Benchmark('List-Drop', 'drop first $n$ elements', '0, inc, dec'),
        Benchmark('List-Delete', 'delete value'),
        Benchmark('List-Map', 'map'),
        Benchmark('List-Zip', 'zip'),
        Benchmark('List-ZipWith', 'zip with function'),
        Benchmark('List-ToNat', 'absolute values', 'neg, map'),
        Benchmark('List-Product', 'cartesian product', 'append, map'),
        Benchmark('List-Snoc', 'insert at end'),
        Benchmark('List-Reverse', 'reverse', 'insert at end'),
        Benchmark('List-Foldr', 'fold'),
        Benchmark('List-Fold-Length', 'length using fold', '0, inc, dec', ['-m=0']),
        Benchmark('List-Fold-Append', 'append using fold', '', ['-m=0'])
        ]),
]

class SynthesisResult:
    def __init__(self, name, time, code_size, spec_size, measure_count, component_count):
        self.name = name                        # Benchmark name
        self.time = time                        # Synthesis time (seconds)
        self.code_size = code_size              # Synthesized code size (in AST nodes)
        self.spec_size = spec_size              # Specification size (in AST nodes)
        self.measure_count = measure_count      # Number of measures defined
        self.component_count = component_count  # Number of components provided
        self.variant_times = {                  # Synthesis times for Synquid variants:
                                'def': 0.0,         # in common context
                                'nis': 0.0,         # with no incremental solving
                                'ncc': 0.0,         # with no consistency checks
                                'nuc': 0.0,         # with no UNSAT-core based solving
                                'nm': 0.0           # with no memoization
                             }

    def str(self):
        return self.name + ', ' + '{0:0.2f}'.format(self.time) + ', ' + self.code_size + ', ' + self.spec_size + ', ' + self.measure_count + ', ' + self.component_count

def run_benchmark(name, opts):
    '''Run benchmark name with command-line options opts; record results in the results dictionary'''

    with open(LOGFILE_NAME, 'a+') as logfile:
      start = time.time()
      logfile.write(name + '\n')
      logfile.seek(0, os.SEEK_END)
      # Run Synquid on the benchmark:
      return_code = call([SYNQUID_CMD] + COMMON_OPTS + opts + [name + '.sq'], stdout=logfile, stderr=logfile)
      end = time.time()

      print '{0:0.2f}'.format(end - start),
      if return_code: # Synthesis failed
          print Back.RED + Fore.RED + Style.BRIGHT + 'FAIL' + Style.RESET_ALL,
          results [name] = SynthesisResult(name, (end - start), '-', '-', '-', '-')
      else: # Synthesis succeeded: code metrics from the output and record synthesis time
          lastLines = os.popen("tail -n 5 %s" % LOGFILE_NAME).read().split('\n')
          solution_size = re.match("\(Size: (\d+)\).*$", lastLines[0]).group(1)
          spec_size = re.match("\(Spec size: (\d+)\).*$", lastLines[1]).group(1)
          measures = re.match("\(#measures: (\d+)\).*$", lastLines[2]).group(1)
          components = re.match("\(#components: (\d+)\).*$", lastLines[3]).group(1)
          results [name] = SynthesisResult(name, (end - start), solution_size, spec_size, measures, components)
          print Back.GREEN + Fore.GREEN + Style.BRIGHT + 'OK' + Style.RESET_ALL,

      print

if __name__ == '__main__':
    init()
    results = {}

    # Delete old log file
    if os.path.isfile(LOGFILE_NAME):
      os.remove(LOGFILE_NAME)

    # Run experiments
    # Note this version of the script only runs Synquid with all optimizations enabled and in benchmark-specific context
    # and on a reduced set of fast benchmarks
    for group in ALL_BENCHMARKS:
        for b in group.benchmarks:
            print b.str()
            run_benchmark(b.name, b.options)

    # Compare with previous solutions and print the diff
    if os.path.isfile(ORACLE_NAME):
        fromlines = open(ORACLE_NAME).readlines()
        tolines = open(LOGFILE_NAME, 'U').readlines()
        diff = difflib.unified_diff(fromlines, tolines, n=0)
        print
        sys.stdout.writelines(diff)
