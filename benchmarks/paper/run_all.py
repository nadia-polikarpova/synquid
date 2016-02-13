import sys
import os, os.path
import platform
import shutil
import time
import re
import difflib
from subprocess import call, check_output, STDOUT
from colorama import init, Fore, Back, Style

# Parameters
SYNQUID_PATH_LINUX = '../../dist/build/synquid/synquid'
SYNQUID_PATH_WINDOWS = '../../src/Synquid.exe'
BENCH_PATH = '.'
LOGFILE_NAME = 'run_all.log'
ORACLE_NAME_WINDOWS = 'oracle'
ORACLE_NAME_LINUX = 'oracle_nx'
OUTFILE_NAME = 'run_all.csv'
COMMON_OPTS = ['--print-solution-size=True', '--print-spec-size=True']
BFS_ON_OPT = ['--bfs=1']
INCREMENTAL_OFF_OPT = ['--incremental=0']
CONSISTENCY_OFF_OPT = ['--consistency=0']
MEMOIZATION_ON_OPT = ['--use-memoization=1']
TIMEOUT_COMMAND = 'timeout'
TIMEOUT= '2'
FNULL = open(os.devnull, 'w')

BENCHMARKS = [
    # Integers
    ["Integer", [],
        [('Int-Max2', 'maximum of 2 elements', []),
        ('Int-Max3', 'maximum of 3 elements', []),
        ('Int-Max4', 'maximum of 4 elements', []),
        ('Int-Max5', 'maximum of 5 elements', []),
        ('Int-Add', 'addition', [])]
    ],
    # Lists
    ["List", [],
        [('List-Null', 'is list empty', []),
        ('List-Elem', 'contains an element', []),
        ('List-Stutter', 'duplicate each element', []),
        ('List-Replicate', 'list of element repetitions', []),
        ('List-Append', 'append two lists', ['-m=1']),
        ('List-Concat', 'concatenate list of lists', []),
        ('List-Take', 'take first n elements', []),
        ('List-Drop', 'drop first n elements', []),
        ('List-Delete', 'delete given element', []),
        ('List-Map', 'list map', []),
        ('List-ZipWith', 'list zip with', []),
        ('List-Zip', 'zip two lists', []),
        ('List-ToNat', 'list of integers to nats', []),
        ('List-Product', 'Cartesian product', [])]
    ],
    # Unique lists
    ["Unique list",  ['-f=FirstArgument'],
        [('UniqueList-Insert', 'insertion', []),
        ('UniqueList-Delete', 'deletion', []),
        ('List-Nub', 'deduplication', ['-f=FirstArgument', '-m=1']),
        ('List-Compress', 'dedup subsequences', ['-h'])]
    ],
    ["Sorting",  ['-a=2', '-m=3', '-s=1'],
        # Insertion Sort
        [('IncList-Insert', 'insertion', []),
        ('IncList-InsertSort', 'insertion sort', []),
        ('StrictIncList-Insert', 'insertion (strict order)', []),
        ('StrictIncList-Delete', 'deletion (strict order)', []),
        # Merge sort
        ('List-Split', 'balanced split', ['-s=1', '-m=3']),
        ('IncList-Merge', 'sorted merge', ['-h']),
        ('IncList-MergeSort', 'merge sort', ['-a=2', '-s=1', '-m=3']),
        # Quick sort
        ('List-Partition', 'partition', ['-s=1']),
        ('IncList-PivotAppend', 'append pivot', []),
        ('IncList-QuickSort', 'quick sort', ['-a=2', '-s=1'])]
    ],
    # Trees
    ["Trees",  [],
        [('Tree-Elem', 'membership',[]),
        ('Tree-ToList', 'flatten to a list', []),
        ('Tree-BalancedReplicate', 'create balanced tree', [])]
    ],
    ["BST", ['-m=1', '-e', '-a=2'],
        [# Binary search tree
        ('BST-Member', 'membership', []),
        ('BST-Insert', 'insertion', []),
        # works with: -m=2 -e (fast), -m=2 slower
        ('BST-Delete', 'deletion', ['-m=1', '-e', '-a=2']),
        ('BST-Sort', 'BST sort', [])]
    ],
    ["RBT", ['-m=2', '-a=2', '-u', '-h', '-f=DisableFixpoint'],
        [('RBT-Constructors', 'constructors', ['-m=0', '-a=2']),
        ('RBT-BalanceL', 'balance left', ['-m=1', '-a=2', '-u', '-h', '-f=DisableFixpoint']),
        ('RBT-BalanceR', 'balance right', ['-m=1', '-a=2', '-u', '-h', '-f=DisableFixpoint']),
        ('RBT-Balance', 'balance', ['-m=2', '-a=2', '-u', '-h', '-f=DisableFixpoint'])]
        #('RBT-Ins', ['-m=1', '-a=2', '-e'])
    ],
    ["Heap", [],
        # Binary heap
        [('BinHeap-Member', 'membership', []),
        ('BinHeap-Insert', 'insertion', []),
        ('BinHeap-Doubleton', 'constructor', []),
        ('BinHeap-Tripleton', 'constructor, 3 args', [])]
    ],
    ["User", [],
        # Evaluation
        [('Evaluator', 'desugar AST', [])]
    ]
]

ABS_BENCHMARKS = [
    # Integers
    ["Integer", [],
      [('Int-Max', 'maximum of 2 elements (abs)', [])]
    ],
    # Lists
    ["List", [],
      [('List-Reverse', 'reverse a list', []),
      ('List-Fold', 'length with fold', ['-e'])]
    ],
    # Insertion Sort
    ["Sorting", [],
      [('IncList-Insert', 'insertion sort (abs)', [])]
    ]
]

COMPONENTS = {
   "Int-Add": "integer",
   "List-Null": "bool",
   "List-Elem": "bool",
   "List-Replicate": "integer",
   "List-Take": "integer",
   "List-Drop": "integer",
   "List-Concat": "append",
   "List-ToNat": "map, negate",
   "List-Product": "map, append",
   "List-Nub": "bool, elem",
   "Tree-Elem": "bool",
   "Tree-Flatten": "append",
   "Tree-HBal": "integer",
   "IncList-InsertSort": "insert",
   "IncList-MergeSort": "split, merge",
   "IncList-QuickSort": "partition, pivot append",
   "BST-Member": "bool",
   "BST-Sort": "toBST, flatten, insert, merge",
   "BST-Delete": "merge",
   "Evaluator": "integer",
   "Evaluator-Vars": "integer",
}

class SynthesisResult:
    def __init__(self, name, time, size, specSize, nMeasures, nComponents):
        self.name = name
        self.time = time
        self.size = size
        self.specSize = specSize
        self.nMeasures = nMeasures
        self.nComponents = nComponents
        self.otherTimes = [0.0, 0.0, 0.0, 0.0, 0.0]

    def str(self):
        return self.name + ', ' + '{0:0.2f}'.format(self.time) + ', ' + self.size + ', ' + self.specSize + ', ' + self.nMeasures + ', ' + self.nComponents

def run_version(name, opts, path, logfile, versionInd, versionParameter):
  start = time.time()
  logfile.seek(0, os.SEEK_END)
  # execute but mute output
  return_code = call([TIMEOUT_COMMAND] + [TIMEOUT] + [synquid_path] + COMMON_OPTS +
    versionParameter + [path + name + '.sq'], stdout=FNULL, stderr=STDOUT)
  end = time.time()

  print '{0:0.2f}'.format(end - start),
  if return_code == 124:
      print Back.RED + Fore.RED + Style.BRIGHT + 'TIMEOUT' + Style.RESET_ALL,
      results[name].otherTimes[versionInd] = -1
  elif return_code:
      print Back.RED + Fore.RED + Style.BRIGHT + 'FAIL' + Style.RESET_ALL,
      results[name].otherTimes[versionInd] = -2
  else:
      results[name].otherTimes[versionInd] = (end - start)
      print Back.GREEN + Fore.GREEN + Style.BRIGHT + 'OK' + Style.RESET_ALL,

def run_benchmark(name, opts, defOpts, path=''):
    print name,

    with open(LOGFILE_NAME, 'a+') as logfile:
      start = time.time()
      logfile.write(path + name + '\n')
      logfile.seek(0, os.SEEK_END)
      return_code = call([synquid_path] + COMMON_OPTS + opts + [path + name + '.sq'], stdout=logfile, stderr=logfile)
      end = time.time()

      print '{0:0.2f}'.format(end - start),
      if return_code:
          print Back.RED + Fore.RED + Style.BRIGHT + 'FAIL' + Style.RESET_ALL,
          results [name] = SynthesisResult(name, (end - start), "-", "-", "-", "-")
      else:
          lastLines = os.popen("tail -n 5 %s" % LOGFILE_NAME).read().split('\n')
          solutionSize = re.match("\(Size: (\d+)\).*$", lastLines[0]).group(1)
          specSize = re.match("\(Spec size: (\d+)\).*$", lastLines[1]).group(1)
          measures = re.match("\(#measures: (\d+)\).*$", lastLines[2]).group(1)
          components = re.match("\(#components: (\d+)\).*$", lastLines[3]).group(1)
          results [name] = SynthesisResult(name, (end - start), solutionSize, specSize, measures, components)
          print Back.GREEN + Fore.GREEN + Style.BRIGHT + 'OK' + Style.RESET_ALL,

      versions = [(defOpts, 4), (BFS_ON_OPT, 0), (INCREMENTAL_OFF_OPT, 1),
        (CONSISTENCY_OFF_OPT, 2), (MEMOIZATION_ON_OPT, 3)]

      for (opts, versionInd) in versions:
        run_version(name, opts, path, logfile, versionInd, opts)

      print

def postprocess(benchmarks):
    with open(OUTFILE_NAME, 'w') as outfile:
        for arr in benchmarks:
            category = arr[0]
            benchArray = arr[2]
            outfile.write ('\multirow{')
            outfile.write (str(benchArray.__len__()))
            outfile.write ('}{*}[-2pt]{\\rotatebox{90}{')
            outfile.write (category)
            outfile.write ('}}')
            for (name, tableName, args) in benchArray:
                if name in results:
                    res = results [name]
                    outfile.write (' & ')
                    outfile.write (tableName)
                    outfile.write (' & ')
                    row = \
                    res.specSize + \
                    ' & ' + res.nMeasures + '& ' + res.nComponents + \
                    ' & ' + COMPONENTS.get(name, '') + \
                    ' & ' + res.size + '& ' + '{0:0.2f}'.format(res.time) + \
                    ' & ' + '{0:0.2f}'.format(res.otherTimes[3])  + '& ' + '{0:0.2f}'.format(res.otherTimes[2]) + \
                    ' & ' + '{0:0.2f}'.format(res.otherTimes[0]) + '& ' + \
                    ' & ' + '{0:0.2f}'.format(res.otherTimes[4]) + '& ' + \
                    '{0:0.2f}'.format(res.otherTimes[1]) + ' \\\\'
                    outfile.write (row)
                outfile.write ('\n')
            outfile.write ('\\hline')

if __name__ == '__main__':
    init()
    results = {}

    if platform.system() == 'Linux':
        synquid_path = SYNQUID_PATH_LINUX
        oracle_name = ORACLE_NAME_LINUX
    else:
        synquid_path = SYNQUID_PATH_WINDOWS
        oracle_name = ORACLE_NAME_WINDOWS

    if os.path.isfile(LOGFILE_NAME):
      os.remove(LOGFILE_NAME)

    allBenchmarks = [('Normal benchmarks', BENCHMARKS, ''), ('Abstract refinements', ABS_BENCHMARKS, '../abstract/')]

    for (benchmarkCategory, benchmarks, dirPrefix) in allBenchmarks:
      print Back.YELLOW + Fore.YELLOW + Style.BRIGHT + benchmarkCategory + Style.RESET_ALL
      benchmarkArray = [ (item, array[1]) for array in benchmarks for item in array[2]]
      #print([str(item) for item in benchmarkArray])
      for ((name, _, args), defOpts) in benchmarkArray:
          #print(str(name) + str(args))
          run_benchmark(name, args, defOpts, dirPrefix)
      postprocess(benchmarks)

    if os.path.isfile(oracle_name):
        fromlines = open(oracle_name).readlines()
        tolines = open(LOGFILE_NAME, 'U').readlines()
        diff = difflib.unified_diff(fromlines, tolines, n=0)
        print
        sys.stdout.writelines(diff)
