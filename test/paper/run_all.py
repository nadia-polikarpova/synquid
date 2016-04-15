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
if platform.system() in ['Linux', 'Darwin']:
    SYNQUID_CMD = './synquid'                                     # Command to call Synquid
    TIMEOUT_CMD = 'timeout'                                     # Timeout command
    TIMEOUT = '1'                                             # Timeout value (seconds)    
else:
    SYNQUID_CMD = 'Synquid.exe'
    TIMEOUT_CMD = ''
    TIMEOUT = ''

LOGFILE_NAME = 'run_all.log'                                    # Log file
OUTFILE_NAME = 'results.tex'                                    # Latex table with experiment results
ORACLE_NAME = 'solutions'                                       # Solutions file
COMMON_OPTS = ['--print-solution-size', 
               '--print-spec-size',
               '--memoize']                                     # Options to use for all benchmarks
BFS_ON_OPT = ['--bfs-solver']                                   # Option to disable UNSAT-core based solver
INCREMENTAL_OFF_OPT = ['--incremental=0']                       # Option to disable incremental solving
CONSISTENCY_OFF_OPT = ['--consistency=0']                       # Option to disable consistency checks
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
    BenchmarkGroup("List", [], [
        Benchmark('List-Null', 'is empty', 'true, false'),
        Benchmark('List-Elem', 'is member', 'true, false, $=$, $\\neq$'),
        Benchmark('List-Stutter', 'duplicate each element'),
        Benchmark('List-Replicate', '$n$ copies of value', '0, inc, dec, $\\leq$, $\\neq$'),
        Benchmark('List-Append', 'append two lists', '', ['-m=1']),
        Benchmark('List-Concat', 'concatenate list of lists', 'append'),
        Benchmark('List-Take', 'take first $n$ elements', '0, inc, dec, $\\leq$, $\\neq$'),
        Benchmark('List-Drop', 'drop first $n$ elements', '0, inc, dec, $\\leq$, $\\neq$'),
        Benchmark('List-Delete', 'delete value', '$=$, $\\neq$'),
        Benchmark('List-Map', 'map'),
        Benchmark('List-Zip', 'zip'),
        Benchmark('List-ZipWith', 'zip with function'),
        Benchmark('List-Product', 'cartesian product', 'append, map'),
        Benchmark('List-Ith', '$i$-th element', '0, inc, dec, $\\leq$, $\\neq$'),
        Benchmark('List-ElemIndex', 'index of element', '0, inc, dec, $=$, $\\neq$'),
        Benchmark('List-Snoc', 'insert at end'),
        Benchmark('List-Reverse', 'reverse', 'insert at end'),
        Benchmark('List-Foldr', 'foldr'),
        Benchmark('List-Fold-Length', 'length using fold', '0, inc, dec', ['-m=0']),
        Benchmark('List-Fold-Append', 'append using fold', '', ['-m=0'])
        ]),
    BenchmarkGroup("Unique list", [], [
        Benchmark('UniqueList-Insert', 'insert', '$=$, $\\neq$'),
        Benchmark('UniqueList-Delete', 'delete', '$=$, $\\neq$'),
        Benchmark('List-Nub', 'remove duplicates', 'is member', ['-m=1']),
        Benchmark('List-Compress', 'remove adjacent dupl.', '$=$, $\\neq$'),
        Benchmark('UniqueList-Range', 'integer range', '0, inc, dec, $\\leq$, $\\neq$'),
        ]),
    BenchmarkGroup("Strictly sorted list", [], [
        Benchmark('StrictIncList-Insert', 'insert', '$<$'),
        Benchmark('StrictIncList-Delete', 'delete', '$<$'),
        Benchmark('StrictIncList-Intersect', 'intersect', '$<$', ['-f=AllArguments']),
        ]),
    BenchmarkGroup("Sorting",  ['-a=2', '-m=3', '-f=AllArguments'], [
        # Insertion Sort
        Benchmark('IncList-Insert', 'insert (sorted)', '$\\leq$, $\\neq$'),
        Benchmark('List-InsertSort', 'insertion sort', 'insert (sorted)'),
        Benchmark('List-Fold-Sort', 'sort by folding', 'foldr, $\\leq$, $\\neq$', ['-m=1', '-a=2', '-e']),
        # Selection Sort
        Benchmark('List-ExtractMin', 'extract minimum', '$\\leq$, $\\neq$', ['-a=2', '-m 3']),
        Benchmark('List-SelectSort', 'selection sort', 'extract minimum'),        
        # Merge sort
        Benchmark('List-Split', 'balanced split', '', ['-m=3']),
        Benchmark('IncList-Merge', 'merge', '$\\leq$, $\\neq$', ['-f=AllArguments']),
        Benchmark('List-MergeSort', 'merge sort', 'split, merge', ['-a=2', '-m=3']),
        # Quick sort
        Benchmark('List-Partition', 'partition', '$\\leq$'),
        Benchmark('IncList-PivotAppend', 'append with pivot'),
        Benchmark('List-QuickSort', 'quick sort', 'partition, append w/pivot', ['-a=2'])
        ]),
    BenchmarkGroup("Trees",  [], [
        Benchmark('Tree-Elem', 'is member', 'false, not, or, $=$'),
        Benchmark('Tree-Count', 'node count', '0, 1, +'),
        Benchmark('Tree-ToList', 'preorder', 'append'),
        Benchmark('Tree-BalancedReplicate', 'create balanced', '0, inc, dec, $\\leq$, $\\neq$')
        ]),
    BenchmarkGroup("BST", [], [
        Benchmark('BST-Member', 'is member', 'true, false, $\\leq$, $\\neq$'),
        Benchmark('BST-Insert', 'insert', '$\\leq$, $\\neq$'),
        Benchmark('BST-Delete', 'delete', '$\\leq$, $\\neq$', ['-e']),
        Benchmark('BST-Sort', 'BST sort', '$\\leq$, $\\neq$')
        ]),
    BenchmarkGroup("Bin Heap", [], [
        Benchmark('BinHeap-Member', 'is member', 'false, not, or, $\\leq$, $\\neq$'),
        Benchmark('BinHeap-Insert', 'insert', '$\\leq$, $\\neq$'),
        Benchmark('BinHeap-Singleton', '1-element constructor', '$\\leq$, $\\neq$'),
        Benchmark('BinHeap-Doubleton', '2-element constructor', '$\\leq$, $\\neq$'),
        Benchmark('BinHeap-Tripleton', '3-element constructor', '$\\leq$, $\\neq$')
        ]),
    BenchmarkGroup("AVL", ['-a=2'], [
        Benchmark('AVL-RotateL', 'rotate left', 'inc', ['-a 2', '-u']),
        Benchmark('AVL-RotateR', 'rotate right', 'inc', ['-a 2', '-u']),
        Benchmark('AVL-Balance', 'balance', 'rotate left, rotate right', ['-a 2', '-e']),
        Benchmark('AVL-Insert', 'insert', 'balance, $<$', ['-a 2']),
        Benchmark('AVL-ExtractMin', 'extract minimum', '$<$', ['-a 2']),
        Benchmark('AVL-Delete', 'delete', 'extract minimum, balance, $<$', ['-a 2', '-m 1']),
        ]),        
    BenchmarkGroup("RBT", ['-m=1', '-a=2', '-u'], [
        Benchmark('RBT-BalanceL', 'balance left', '', ['-m=1', '-a=2', '-u']),
        Benchmark('RBT-BalanceR', 'balance right', '', ['-m=1', '-a=2', '-u']),
        Benchmark('RBT-Insert', 'insert', 'balance left, right, $\\leq$, $\\neq$', ['-m=1', '-a=2', '-u'])
        ]),
    BenchmarkGroup("User", [], [
        Benchmark('Evaluator', 'desugar AST', '0, 1, 2'),
        Benchmark('AddressBook-Make', 'make address book', 'is private', ['-a=2']),
        Benchmark('AddressBook-Merge', 'merge address books', 'append', ['-a=2'])
        ])
]

# mapping by benchmark name looks sufficient
SOLUTION_COMPONENTS = {
  'RBT-Insert' : '3',
  'AVL-RotateL' : '3',
  'BST-Sort' : '5',
  'RBT-BalanceL' : '2'
  , 'List-Nub' : '2'
  , 'AVL-Delete' : '2'
  , 'RBT-BalanceR' : '2'
  , 'AVL-RotateR' : '3'
  , 'RBT-Insert' : '3'
}

class SynthesisResult:
    def __init__(self, name, time, code_size, spec_size, measure_count, component_count = '1'):
        self.name = name                        # Benchmark name
        self.time = time                        # Synthesis time (seconds)
        self.code_size = code_size              # Synthesized code size (in AST nodes)
        self.spec_size = spec_size              # Specification size (in AST nodes)
        self.measure_count = measure_count      # Number of measures defined
        # Number of components provided
        if name in SOLUTION_COMPONENTS: self.component_count = SOLUTION_COMPONENTS[name]
        else: self.component_count = component_count  
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
          # components of the solution (rather than synthesis components)          
          #components = re.match("\(#components: (\d+)\).*$", lastLines[3]).group(1)
          results [name] = SynthesisResult(name, (end - start), solution_size, spec_size, measures)
          print Back.GREEN + Fore.GREEN + Style.BRIGHT + 'OK' + Style.RESET_ALL,

      variant_options = [   # Command-line options to use for each variant of Synquid
            ('def', default_opts),
            ('nis', opts + INCREMENTAL_OFF_OPT),
            ('ncc', opts + CONSISTENCY_OFF_OPT),
            ('nuc', opts + BFS_ON_OPT)
        ]

      # Run each variant:
      if platform.system() in ['Linux', 'Darwin']:
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
                    b.components + \
                    ' & ' + result.spec_size + \
                    ' & ' + result.measure_count + \
                    ' & ' + result.component_count + \
                    ' & ' + result.code_size + \
                    ' & ' + '{0:0.2f}'.format(result.time) + \
                    ' & ' + '{0:0.2f}'.format(result.variant_times['def']) + \
                    ' & ' + '{0:0.2f}'.format(result.variant_times['nis']) + \
                    ' & ' + '{0:0.2f}'.format(result.variant_times['ncc']) + \
                    ' & ' + '{0:0.2f}'.format(result.variant_times['nuc']) + ' \\\\'
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

    # Print additional info about experiments
    num_benchmarks = sum([len(g.benchmarks) for g in ALL_BENCHMARKS])
    # TODO -- get rid of hardcoded 5
    sys.stdout.write('Total number of benchmarks: ' + str(num_benchmarks * 5) + '\n')
    num_TOs = sum([sum([len([r for r in results[n.name].variant_times.values() if r < 0.0]) for n
      in g.benchmarks]) for g in ALL_BENCHMARKS])
    #num_TOs = [[[r for r in filter(lambda k: k >= 0, results[n.name].variant_times.values())] for n
    #  in g.benchmarks] for g in ALL_BENCHMARKS]
    sys.stdout.write('Total number of timeouts: ' + str(num_TOs) + '\n')
