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

LIFTY       = ['synquid', 'lifty', '--print-stats']
OUT_DIR     = 'out'
PRELUDE_LIB = 'Prelude.sq'
TIO_LIB     = 'Tagged.sq'
CONF_LIB    = os.path.join('conference', 'Conference.sq')   
GRADR_LIB   = os.path.join('gradr', 'Models.sq')

MICRO_TABLES = [os.path.join(OUT_DIR, 'microbenchmarks', '01-EDAS.out'),
                os.path.join(OUT_DIR, 'microbenchmarks', '02-Multiple.out'), 
                os.path.join(OUT_DIR, 'microbenchmarks', '03-SelfRef.out'), 
                os.path.join(OUT_DIR, 'microbenchmarks', '04-Search.out'),
                os.path.join(OUT_DIR, 'microbenchmarks', '05-Sort.out'),
                os.path.join(OUT_DIR, 'microbenchmarks', '06-Broadcast.out'),
                os.path.join(OUT_DIR, 'microbenchmarks', '07-HotCRP.out'),
                os.path.join(OUT_DIR, 'microbenchmarks', '08-AirBnB.out'),
                os.path.join(OUT_DIR, 'microbenchmarks', '09-Instagram.out')]
CONF_TABLES = [os.path.join(OUT_DIR, 'conference', 'ConferenceRepair.out'), 
               os.path.join(OUT_DIR, 'conference', 'ConferenceVerification.out')]
GRADR_TABLES = [os.path.join(OUT_DIR, 'gradr', 'Gradr.out')]
HEALTH_TABLES = [os.path.join(OUT_DIR, 'health', 'HealthWeb.out')]

MICRO_METAPROGRAM = {
  'columns':         ["num(key)", "micro(key)", "$1", "(#2-#1)", "sum_sec($3)", "sum_sec($4,$5)", "sum_sec($6)"],
  'rows': ["01-EDAS:showSession",
           "02-Multiple:showSession",
           "03-SelfRef:showSession",
           "04-Search:showMyAcceptedPapers",
           "05-Sort:sortPapersByScore",
           "06-Broadcast:notifyAuthors",
           "07-HotCRP:sendPasswordReminder",
           "08-AirBnB:viewInbox",
           "09-Instagram:showRecommendations"
           ],
  'fmt': ["%-2s", " \\d%-20s", "%s", "%8s", "%8s", "%10s", "%10s"],
  'helpers': {
    'num': (lambda txt: int(txt.split('-')[0])),
    'micro': (lambda txt: "{micro%s}" % txt.split('-')[0]),
    'sum_sec': lambda *a: "%.1fs" % sum(secs(*a)),
  }
}

CONF_METAPROGRAM = {
  'columns':         ["braces(key)", "$1", "(#2'-#1)", "(#2-#1)", "sum_sec($3')", "sum_sec($3)", "sum_sec($4,$5)", "sum_sec($6)"],
  'rows': ["registerUser",
           "usersView",
           "submitForm",
           "searchForm",
           "paperView",
           "reviewsView",
           "profileViewGet",
           "profileViewPost",
           "submitReviewViewPost",
           "assignReviewersView",
           "Totals"],
  'fmt': ["%-30s", "%s", "%8s", "%8s", "%10s", "%10s", "%10s", "%10s"],
  'helpers': {
    'nonneg': (lambda n: max(0, n)),
    'sum_sec': lambda *a: "%.1fs" % sum(secs(*a)),
    'braces': (lambda txt: (r"%s\st" if txt == 'Totals' else r"\d{%s}") % txt)
  }
}

GRADR_METAPROGRAM = {
  'columns':         ["braces(key)", "$1", "(#2-#1)", "sum_sec($3)", "sum_sec($4, $5)", "sum_sec($6)"],
  'rows': ["homePage",
           "profileView",
           "unauthProfileView",
           "scoresForAssignmentView",
           "topScoreForAssignmentView",
           "scoresForStudentView",           
           "Totals"],
  'fmt': ["%-40s", "%s", "%8s", "%10s", "%10s", "%10s"],
  'helpers': {
    'nonneg': (lambda n: max(0, n)),
    'sum_sec': lambda *a: "%.1fs" % sum(secs(*a)),
    'braces': (lambda txt: (r"%s\st" if txt == 'Totals' else r"\d{%s}") % txt)
  }
}

HEALTH_METAPROGRAM = GRADR_METAPROGRAM.copy()
HEALTH_METAPROGRAM.update({
    'rows': ["showRecordByIdView",
             "showRecordsForPatientView",
             "showAuthoredRecordsView",
             "updateRecordForm",
             "listOfPatientsView",
             "Totals"]
})   

# Running benchmarks

def run_benchmark(path, name, opts, function=''):    
    only = [] if function == '' else ['--only', function]
    out_dir = os.path.join (OUT_DIR, path)
    logfile_name = name if function == '' else function
    if not os.path.exists(out_dir):
      os.makedirs(out_dir)    

    with open(os.path.join (out_dir, logfile_name + '.out'), 'w') as logfile:      
      # os.chdir(path)    
      print name, function,
      sys.stdout.flush()
      start = time.time()
      return_code = call(LIFTY + opts + ['--file', os.path.join (path, name + '.sq')] + only, stdout=logfile, stderr=logfile)
      end = time.time()
      
      if return_code:
          print Back.RED + Fore.RED + Style.BRIGHT + 'FAIL' + Style.RESET_ALL,
      else:
          print Back.GREEN + Fore.GREEN + Style.BRIGHT + 'OK' + Style.RESET_ALL,
      print '{0:0.1f}'.format(end - start), 'sec'
      
# Extracting latex tables from output

def dictadd(*a):
    d = {}
    for x in a: d.update(x)
    return d

def secs(*b):
    """auxiliary for processing time entries"""
    for el in b:
        idx = el.find('s')
        assert idx > 0
        yield float(el[:idx])

def parse_table(fn):
    txt = open(fn).read()
    # assume that the table is separated from the rest of the text (if any) by a blank line
    txt = txt.split("\n\n")[-1]
    return dictadd({'filename': fn},
                   {s[0].strip(): s for s in [line.split("  &") for line in txt.splitlines()]})

def concat_tables(tables):
    d = {}
    for t in tables:
        try:
            prefix = os.path.splitext(os.path.basename(t['filename']))[0]
            d.update({(prefix+":"+k): v for k,v in t.iteritems()})
        except KeyError:
            d.update(t)
    return d

def eval_expr(expr, value, key=None, helpers={}):
    expr = re.sub(r'\$(\d+)\'', lambda m: "_[1][%s]" % m.group(1), expr)
    expr = re.sub(r'\$(\d+)',   lambda m: "_[0][%s]" % m.group(1), expr)
    expr = re.sub(r'#(\d+)\'',  lambda m: "int(_[1][%s])" % m.group(1), expr)
    expr = re.sub(r'#(\d+)',    lambda m: "int(_[0][%s])" % m.group(1), expr)
    try:
        return eval(expr, dictadd({'_': value, 'key': key}, helpers))
    except:
        import traceback
        traceback.print_exc()
        return "??"


class Program(object):
    
    def __init__(self, metaprogram):
        self.metaprogram = metaprogram

    def eval_meta(self, tables):
        out = []
        for rowh in self.metaprogram['rows']:
            row = [table.get(rowh, []) for table in tables]
            out.append([eval_expr(e, row, rowh, self.metaprogram['helpers']) for e in self.metaprogram['columns']])
            
        return out
    
    def fmt_output(self, table):
        fmt = "  &".join(self.metaprogram['fmt'])
        def endslash(s):
            if s.endswith("\\\\"): return s 
            else: return s + "  \\\\"
        for row in table:
            print endslash(fmt % tuple(map(unicode, row)))
            
# Main

def run_all_benchmarks():
    if not os.path.exists(OUT_DIR):
      os.makedirs(OUT_DIR)
    
    print 'Verifying Lifty standard library...'
    run_benchmark('.', 'Prelude', ['--verify'])
    run_benchmark('.', 'Tagged', ['--verify', '--libs', PRELUDE_LIB])
    print
    
    print 'Running verification benchmarks...'
    for fn in ['ok1', 'ok2', 'ok3', 'ok4', 'bad1', 'bad2', 'bad3', 'bad4']:
      run_benchmark('verify', 'Test', ['--verify', '--libs', PRELUDE_LIB, '--libs', TIO_LIB], fn)
    for bench in os.listdir('verify'): 
      if os.path.isfile(os.path.join('verify', bench)):
        filename, file_extension = os.path.splitext(bench)
        if file_extension == '.sq' and filename != 'Test':
          run_benchmark('verify', filename, ['--verify', '--libs', PRELUDE_LIB, '--libs', TIO_LIB])    
    print
    
    print 'Running repair benchmarks...'
    for bench in os.listdir('microbenchmarks'): 
      if os.path.isfile(os.path.join('microbenchmarks', bench)):
        filename, file_extension = os.path.splitext(bench)
        if file_extension == '.sq':
          run_benchmark('microbenchmarks', filename, ['--libs', PRELUDE_LIB, '--libs', TIO_LIB])
    print          
        
    print 'Running case studies...'
    run_benchmark('conference', 'ConferenceVerification', ['--verify', '--libs', PRELUDE_LIB, '--libs', TIO_LIB, '--libs', CONF_LIB])
    run_benchmark('conference', 'ConferenceRepair', ['--libs', PRELUDE_LIB, '--libs', TIO_LIB, '--libs', CONF_LIB])
    run_benchmark('gradr', 'Gradr', ['--libs', PRELUDE_LIB, '--libs', TIO_LIB, '--libs', GRADR_LIB])
    run_benchmark('health', 'HealthWeb', ['--libs', PRELUDE_LIB, '--libs', TIO_LIB])
    
def gen_all_tables():
    print "% Micro benchmarks"
    ctx = [concat_tables(parse_table(fn) for fn in MICRO_TABLES)]  # "in sequence"
    mp = Program(MICRO_METAPROGRAM)
    mp.fmt_output( mp.eval_meta(ctx) )

    # Conference Management
    print "% Conference Management"
    ctx = [parse_table(fn) for fn in CONF_TABLES]  # "in parallel"
    mp = Program(CONF_METAPROGRAM)
    mp.fmt_output( mp.eval_meta(ctx) )
    # Gradr
    print "% Gradr"
    ctx = [parse_table(fn) for fn in GRADR_TABLES]
    mp = Program(GRADR_METAPROGRAM)
    mp.fmt_output( mp.eval_meta(ctx) )
    # HealthWeb
    print "% HealthWeb"
    ctx = [parse_table(fn) for fn in HEALTH_TABLES]
    mp = Program(HEALTH_METAPROGRAM)
    mp.fmt_output( mp.eval_meta(ctx) )    

          
if __name__ == '__main__':
    init()
    
    run_all_benchmarks()
    
    print
    
    gen_all_tables()

        
