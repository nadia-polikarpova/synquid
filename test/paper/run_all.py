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
SYNQUID_CMD = '../../dist/build/synquid/synquid'                                         # Command to call Synquid
LOGFILE_NAME = 'run_all.log'                                    # Log file
OUTFILE_NAME = 'results.tex'                                    # Latex table with experiment results
ORACLE_NAME = 'solutions'                                       # Solutions file
COMMON_OPTS = ['--print-solution-size', '--print-spec-size']    # Options to use for all benchmarks
BFS_ON_OPT = ['--bfs']                                          # Option to disable UNSAT-core based solver
INCREMENTAL_OFF_OPT = ['--incremental=0']                       # Option to disable incremental solving
CONSISTENCY_OFF_OPT = ['--consistency=0']                       # Option to disable consistency checks
MEMOIZATION_ON_OPT = ['--use-memoization']                      # Option to disable memoization
TIMEOUT_CMD = 'timeout'                                         # Timeout command
TIMEOUT= '120'                                                  # Timeout value (seconds)
FNULL = open(os.devnull, 'w')                                   # Null file

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
        Benchmark('Int-Max4', 'maximum of 4'),
        Benchmark('Int-Max5', 'maximum of 5'),
        Benchmark('Int-Add', 'add using increment', '0, inc, dec')
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
    BenchmarkGroup("Unique list", ['-f=FirstArgument'], [
        Benchmark('UniqueList-Insert', 'insert'),
        Benchmark('UniqueList-Delete', 'delete'),
        Benchmark('List-Nub', 'remove duplicates', 'is member', ['-f=FirstArgument', '-m=1']),
        Benchmark('List-Compress', 'remove adjacent dupl.', '', ['-h'])
        ]),
    BenchmarkGroup("Sorting",  ['-a=2', '-m=3', '-s=1'], [
        # Insertion Sort
        Benchmark('IncList-Insert', 'insert (sorted)'),
        Benchmark('IncList-InsertSort', 'insertion sort', 'insert (sorted)'),
        Benchmark('StrictIncList-Insert', 'insert (strictly sorted)'),
        Benchmark('StrictIncList-Delete', 'delete (strictly sorted)'),
        # Merge sort
        Benchmark('List-Split', 'balanced split', '', ['-s=1', '-m=3']),
        Benchmark('IncList-Merge', 'merge', '', ['-h']),
        Benchmark('IncList-MergeSort', 'merge sort', 'split, merge', ['-a=2', '-s=1', '-m=3']),
        # Quick sort
        Benchmark('List-Partition', 'partition', '', ['-s=1']),
        Benchmark('IncList-PivotAppend', 'append with pivot'),
        Benchmark('IncList-QuickSort', 'quick sort', 'partition, append w/pivot', ['-a=2', '-s=1'])
        ]),
    BenchmarkGroup("Trees",  [], [
        Benchmark('Tree-Elem', 'is member', 'false, not, or'),
        Benchmark('Tree-ToList', 'to a list', 'append'),
        Benchmark('Tree-BalancedReplicate', 'create balanced', '0, inc, dec')
        ]),
    BenchmarkGroup("BST", [], [
        Benchmark('BST-Member', 'is member', 'true, false'),
        Benchmark('BST-Insert', 'insert'),
        Benchmark('BST-Delete', 'delete', '', ['-m=1', '-e', '-a=2']),
        Benchmark('BST-Sort', 'BST sort', 'insert, append w/pivot')
        ]),
    BenchmarkGroup("Bin Heap", [], [
        Benchmark('BinHeap-Member', 'is member', 'false, not, or'),
        Benchmark('BinHeap-Insert', 'insert'),
        Benchmark('BinHeap-Singleton', '1-element constructor'),
        Benchmark('BinHeap-Doubleton', '2-element constructor'),
        Benchmark('BinHeap-Tripleton', '3-element constructor')
        ]),
    BenchmarkGroup("RBT", ['-m=1', '-a=2', '-u'], [
        Benchmark('RBT-BalanceL', 'balance left', '', ['-m=1', '-a=2', '-u']),
        Benchmark('RBT-BalanceR', 'balance right', '', ['-m=1', '-a=2', '-u']),
        Benchmark('RBT-Insert', 'insert', 'balance left, right', ['-m=1', '-a=2', '-u'])
        ]),
    BenchmarkGroup("User", [], [
        Benchmark('Evaluator', 'desugar AST', '0, 1, 2'),
        Benchmark('AddressBook-Make', 'make address book', 'is private', ['-a=2']),
        Benchmark('AddressBook-Merge', 'merge address books', 'append', ['-a=2'])
        ])
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

def run_benchmark(name, opts, default_opts):
    '''Run benchmark name with command-line options opts (use default_opts with running the common context variant); record results in the results dictionary'''

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

      variant_options = [   # Command-line options to use for each variant of Synquid
            ('def', default_opts),
            ('nis', opts + INCREMENTAL_OFF_OPT),
            ('ncc', opts + CONSISTENCY_OFF_OPT),
            ('nuc', opts + BFS_ON_OPT),
            ('nm', opts + MEMOIZATION_ON_OPT)
        ]

      # Run each variant:
      for (variant_id, opts) in variant_options:
        run_version(name, variant_id, opts, logfile)

      print

def run_version(name, variant_id, variant_opts, logfile):
    '''Run benchmark name using command-line options variant_opts and record it as a Synquid variant variant_id in the results dictionary'''

    start = time.time()
    logfile.seek(0, os.SEEK_END)
    # Run Synquid on the benchmark, mute output:
    return_code = call([TIMEOUT_CMD] + [TIMEOUT] + [SYNQUID_CMD] + COMMON_OPTS +
        variant_opts + [name + '.sq'], stdout=FNULL, stderr=STDOUT)
    end = time.time()

    print '{0:0.2f}'.format(end - start),
    if return_code == 124:  # Timeout: record timeout
      print Back.RED + Fore.RED + Style.BRIGHT + 'TIMEOUT' + Style.RESET_ALL,
      results[name].variant_times[variant_id] = -1
    elif return_code: # Synthesis failed: record failure
      print Back.RED + Fore.RED + Style.BRIGHT + 'FAIL' + Style.RESET_ALL,
      results[name].variant_times[variant_id] = -2
    else: # Synthesis succeeded: record time for variant
      results[name].variant_times[variant_id] = (end - start)
      print Back.GREEN + Fore.GREEN + Style.BRIGHT + 'OK' + Style.RESET_ALL,


def postprocess():
    '''Generate Latex table from the results dictionary'''

    with open(OUTFILE_NAME, 'w') as outfile:
        for group in ALL_BENCHMARKS:
            outfile.write ('\multirow{')
            outfile.write (str(group.benchmarks.__len__()))
            outfile.write ('}{*}[-2pt]{\\rotatebox{90}{')
            outfile.write (group.name)
            outfile.write ('}}')

            for b in group.benchmarks:
                result = results [b.name]
                outfile.write (' & ')
                outfile.write (b.description)
                outfile.write (' & ')
                row = \
                    result.spec_size + \
                    ' & ' + result.measure_count + \
                    ' & ' + result.component_count + \
                    ' & ' + b.components + \
                    ' & ' + result.code_size + \
                    ' & ' + '{0:0.2f}'.format(result.time) + \
                    ' & ' + '{0:0.2f}'.format(result.variant_times['def']) + \
                    ' & ' + '{0:0.2f}'.format(result.variant_times['nis']) + \
                    ' & ' + '{0:0.2f}'.format(result.variant_times['ncc']) + \
                    ' & ' + '{0:0.2f}'.format(result.variant_times['nuc']) + \
                    ' & ' + '{0:0.2f}'.format(result.variant_times['nm']) + ' \\\\'
                outfile.write (row)
                outfile.write ('\n')
            outfile.write ('\\hline')

if __name__ == '__main__':
    init()
    results = {}

    # Delete old log file
    if os.path.isfile(LOGFILE_NAME):
      os.remove(LOGFILE_NAME)

    # Run experiments
    for group in ALL_BENCHMARKS:
        for b in group.benchmarks:
            print b.str()
            run_benchmark(b.name, b.options, group.default_options)
    # Generate Latex table
    postprocess()

    # Compare with previous solutions and print the diff
    if os.path.isfile(ORACLE_NAME):
        fromlines = open(ORACLE_NAME).readlines()
        tolines = open(LOGFILE_NAME, 'U').readlines()
        diff = difflib.unified_diff(fromlines, tolines, n=0)
        print
        sys.stdout.writelines(diff)
