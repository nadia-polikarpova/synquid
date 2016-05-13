import sys
import os, os.path
import platform
import shutil
import time
import re
import difflib
import pickle
from subprocess import call, check_output, STDOUT
from colorama import init, Fore, Back, Style

# Globals
if platform.system() in ['Linux', 'Darwin']:
    SYNQUID_CMD = './synquid'                                     # Command to call Synquid
    TIMEOUT_CMD = 'timeout'                                     # Timeout command
    TIMEOUT = '120'                                             # Timeout value (seconds)    
else:
    SYNQUID_CMD = 'Synquid.exe'
    TIMEOUT_CMD = ''
    TIMEOUT = ''

LOGFILE = 'results.log'                                         # Log file
DUMPFILE = 'results'                                            # Result serialization file
CSV_FILE = 'result.csv'                                         # CSV-output file
LATEX_FILE = 'results.tex'                                      # Latex-output file
ORACLE_FILE = 'solutions'                                       # Solutions file
COMMON_OPTS = ['--print-stats', 
               '--memoize']                                     # Options to use for all benchmarks
BFS_ON_OPT = ['--bfs-solver']                                   # Option to disable MUSFix
INCREMENTAL_OFF_OPT = ['--incremental=0']                       # Option to disable round-trip type checking
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
        Benchmark('List-Replicate', 'replicate', '0, inc, dec, $\\leq$, $\\neq$'),
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
        Benchmark('List-Nub', 'remove duplicates', 'is member', []),
        Benchmark('List-Compress', 'remove adjacent dupl.', '$=$, $\\neq$'),
        Benchmark('UniqueList-Range', 'integer range', '0, inc, dec, $\\leq$, $\\neq$'),
        ]),
    BenchmarkGroup("Strictly sorted list", ['-f=AllArguments'], [
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
    BenchmarkGroup("Tree",  [], [
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
    BenchmarkGroup("Binary Heap", [], [
        Benchmark('BinHeap-Member', 'is member', 'false, not, or, $\\leq$, $\\neq$'),
        Benchmark('BinHeap-Insert', 'insert', '$\\leq$, $\\neq$'),
        Benchmark('BinHeap-Singleton', '1-element constructor', '$\\leq$, $\\neq$'),
        Benchmark('BinHeap-Doubleton', '2-element constructor', '$\\leq$, $\\neq$'),
        Benchmark('BinHeap-Tripleton', '3-element constructor', '$\\leq$, $\\neq$')
        ]),
    BenchmarkGroup("AVL", ['-a=2'], [
        Benchmark('AVL-RotateL', 'rotate left', 'inc', ['-a 2', '-u']),
        Benchmark('AVL-RotateR', 'rotate right', 'inc', ['-a 2', '-u']),
        Benchmark('AVL-Balance', 'balance', 'rotate, nodeHeight, isSkewed, isLHeavy, isRHeavy', ['-a 2', '-e']),
        Benchmark('AVL-Insert', 'insert', 'balance, $<$', ['-a 2']),
        Benchmark('AVL-ExtractMin', 'extract minimum', '$<$', ['-a 2']),
        Benchmark('AVL-Delete', 'delete', 'extract minimum, balance, $<$', ['-a 2', '-m 1']),
        ]),        
    BenchmarkGroup("RBT", ['-m=1', '-a=2'], [
        Benchmark('RBT-BalanceL', 'balance left', '', ['-m=1', '-a=2']),
        Benchmark('RBT-BalanceR', 'balance right', '', ['-m=1', '-a=2']),
        Benchmark('RBT-Insert', 'insert', 'balance left, right, $\\leq$, $\\neq$', ['-m=1', '-a=2'])
        ]),
    BenchmarkGroup("User", [], [
        Benchmark('Evaluator', 'desugar AST', '0, 1, 2'),
        Benchmark('AddressBook-Make', 'make address book', 'is private', ['-a=2']),
        Benchmark('AddressBook-Merge', 'merge address books', 'append', ['-a=2'])
        ])
]

class SynthesisResult:
    def __init__(self, name, time, goal_count, code_size, spec_size, measure_count):
        self.name = name                        # Benchmark name
        self.time = time                        # Synthesis time (seconds)
        self.goal_count = goal_count            # Number of synthesis goals 
        self.code_size = code_size              # Cumulative synthesized code size (in AST nodes)
        self.spec_size = spec_size              # Cumulative specification size (in AST nodes)
        self.measure_count = measure_count      # Number of measures defined
        self.variant_times = {                  # Synthesis times for Synquid variants:
                                'def': -3.0,         # default exploration bounds
                                'nrt': -3.0,         # round-trip checking disabled
                                'ncc': -3.0,         # consistency checks disabled
                                'nmus': -3.0,        # MUSFix disabled
                             }

    def str(self):
        return self.name + ', ' + '{0:0.2f}'.format(self.time) + ', ' + self.goal_count + ', ' + self.code_size + ', ' + self.spec_size + ', ' + self.measure_count

def run_benchmark(name, opts, default_opts):
    '''Run benchmark name with command-line options opts (use default_opts with running the common context variant); record results in the results dictionary'''

    with open(LOGFILE, 'a+') as logfile:
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
          lastLines = os.popen("tail -n 4 %s" % LOGFILE).read().split('\n')
          goal_count = re.match("\(Goals: (\d+)\).*$", lastLines[0]).group(1)
          measure_count = re.match("\(Measures: (\d+)\).*$", lastLines[1]).group(1)
          spec_size = re.match("\(Spec size: (\d+)\).*$", lastLines[2]).group(1)
          solution_size = re.match("\(Solution size: (\d+)\).*$", lastLines[3]).group(1)                    
          results [name] = SynthesisResult(name, (end - start), goal_count, solution_size, spec_size, measure_count)
          print Back.GREEN + Fore.GREEN + Style.BRIGHT + 'OK' + Style.RESET_ALL,

      variant_options = [   # Command-line options to use for each variant of Synquid
            ('def', default_opts),
            ('nrt', opts + INCREMENTAL_OFF_OPT),
            ('ncc', opts + CONSISTENCY_OFF_OPT),
            ('nmus', opts + BFS_ON_OPT)
        ]

      # Run each variant:
      if (not (cl_opts.medium or cl_opts.small)) and (platform.system() in ['Linux', 'Darwin']):
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
      
def format_time(t):
    if t < 0:
        return '-'
    else:
        return '{0:0.2f}'.format(t)

def write_csv():
    '''Generate CSV file from the results dictionary'''
    with open(CSV_FILE, 'w') as outfile:
        for group in groups:
            for b in group.benchmarks:
                outfile.write (b.name + ',')
                result = results [b.name]
                outfile.write (result.spec_size + ',')
                outfile.write (result.code_size + ',')
                outfile.write (format_time(result.time) + ',')
                outfile.write (format_time(result.variant_times['def']) + ',')
                outfile.write (format_time(result.variant_times['nrt']) + ',')
                outfile.write (format_time(result.variant_times['ncc']) + ',')
                outfile.write (format_time(result.variant_times['nmus']) + ',')
                outfile.write ('\n')

def write_latex():
    '''Generate Latex table from the results dictionary'''
    
    total_count = 0
    to_def = 0
    to_nrt = 0
    to_ncc = 0
    to_nmus = 0

    with open(LATEX_FILE, 'w') as outfile:
        for group in groups:
            outfile.write ('\multirow{')
            outfile.write (str(group.benchmarks.__len__()))
            outfile.write ('}{*}{\\parbox{1cm}{\vspace{-0.85\baselineskip}\center{')
            outfile.write (group.name)
            outfile.write ('}}}')            

            for b in group.benchmarks:
                result = results [b.name]                
                row = \
                    ' & ' + b.description +\
                    ' & ' + result.goal_count +\
                    ' & ' + b.components + \
                    ' & ' + result.measure_count + \
                    ' & ' + result.spec_size + \
                    ' & ' + result.code_size + \
                    ' & ' + format_time(result.time) + \
                    ' & ' + format_time(result.variant_times['def']) + \
                    ' & ' + format_time(result.variant_times['nrt']) + \
                    ' & ' + format_time(result.variant_times['ncc']) + \
                    ' & ' + format_time(result.variant_times['nmus']) + ' \\\\'
                outfile.write (row)
                outfile.write ('\n')
                
                total_count = total_count + 1
                if result.variant_times['def'] < 0.0:
                   to_def = to_def + 1 
                if result.variant_times['nrt'] < 0.0:
                   to_nrt = to_nrt + 1 
                if result.variant_times['ncc'] < 0.0:
                   to_ncc = to_ncc + 1 
                if result.variant_times['nmus'] < 0.0:
                   to_nmus = to_nmus + 1 
                
            outfile.write ('\\hline')
            
    print 'Total:', total_count
    print 'TO def:', to_def
    print 'TO nrt:', to_nrt
    print 'TO ncc:', to_ncc
    print 'TO nmus:', to_nmus
    
def cmdline():
    import argparse
    a = argparse.ArgumentParser()
    a.add_argument('--medium', action='store_true')
    a.add_argument('--small', action='store_true')
    return a.parse_args()    

if __name__ == '__main__':
    init()
    
    cl_opts = cmdline()
    
    # Check if there are serialized results
    if os.path.isfile(DUMPFILE):
        results = pickle.load(open(DUMPFILE, 'r'))
    else:
        results = dict()

    # Delete old log file
    if os.path.isfile(LOGFILE):
      os.remove(LOGFILE)

    # Run experiments
    groups = ALL_BENCHMARKS[:1] if cl_opts.small else ALL_BENCHMARKS
        
    for group in groups:
        for b in group.benchmarks: 
            if b.name in results:
                print b.str() + Back.YELLOW + Fore.YELLOW + Style.BRIGHT + 'SKIPPED' + Style.RESET_ALL
            else:
                print b.str()
                run_benchmark(b.name, b.options, group.default_options)
                with open(DUMPFILE, 'w') as data_dump:
                    pickle.dump(results, data_dump)    
            
    # Generate CSV
    write_csv()            
    # Generate Latex table
    write_latex()

    # Compare with previous solutions and print the diff
    if os.path.isfile(ORACLE_FILE) and (not cl_opts.small):
        fromlines = open(ORACLE_FILE).readlines()
        tolines = open(LOGFILE, 'U').readlines()
        diff = difflib.unified_diff(fromlines, tolines, n=0)
        print
        sys.stdout.writelines(diff)
