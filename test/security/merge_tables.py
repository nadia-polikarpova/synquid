
MICRO_METAPROGRAM = {
  'columns':         ["num(key)", "micro(key)", "$1", "(#2-#1)", "$3", "sum_sec($4,$5)", "$6"],
  'rows': ["01-EDAS.out:showSession",
           "02-Multiple.out:showSession",
           "03-SelfRef.out:showSession",
           "04-Auction.out:showBids",
           "05-StateUpdate.out:placeBid",
           "06-Sort.out:sortPapersByScore",
           "07-Search.out:showMyAcceptedPapers",
           "08-Broadcast.out:notifyAuthors",
           "09-HotCRP.out:sendPasswordReminder",
           "10-AirBnB.out:viewInbox",
           "11-Instagram.out:follow"
           ],
  'fmt': ["%-2s", " \\d%-20s", "%s", "%8s", "%8s", "%10s", "%s"],
  'helpers': {
    'num': (lambda txt: int(txt.split('-')[0])),
    'micro': (lambda txt: "{micro%s}" % txt.split('-')[0]),
    'sum_sec': lambda *a: "%.02fs" % sum(secs(*a)),
  }
}

CONF_METAPROGRAM = {
  'columns':         ["braces(key)", "$1", "(#2'-#1)", "(#2-#1)", "$3'", "$3", "sum_sec($4,$5)", "$6"],
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
  'fmt': ["%-30s", "%s", "%8s", "%8s", "%s", "%s", "%10s", "%s"],
  'helpers': {
    'nonneg': (lambda n: max(0, n)),
    'sum_sec': lambda *a: "%.02fs" % sum(secs(*a)),
    'braces': (lambda txt: (r"%s\st" if txt == 'Totals' else r"\d{%s}") % txt)
  }
}

GRADR_METAPROGRAM = {
  'columns':         ["braces(key)", "$1", "(#2-#1)", "$3", "sum_sec($4, $5)", "$6"],
  'rows': ["homePage",
           "getClassesStdByUser",
           "getClassesInsByUser",
           "getProfileClassInfo",
           "profileView",
           "unauthProfileView",
           "scoresForAssignmentView",
           "scoresForStudentView",
           "getTopScoreForAssignmentView",
           "Totals"],
  'fmt': ["%-40s", "%s", "%8s", "%s", "%10s", "%s"],
  'helpers': {
    'nonneg': (lambda n: max(0, n)),
    'sum_sec': lambda *a: "%.02fs" % sum(secs(*a)),
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

MICRO_TABLES = ["icfp/microbenchmarks/out/01-EDAS.out.txt", 
                "icfp/microbenchmarks/out/02-Multiple.out.txt", 
                "icfp/microbenchmarks/out/03-SelfRef.out.txt", 
                "icfp/microbenchmarks/out/04-Auction.out.txt", 
                "icfp/microbenchmarks/out/05-StateUpdate.out.txt", 
                "icfp/microbenchmarks/out/06-Sort.out.txt",
                "icfp/microbenchmarks/out/07-Search.out.txt",
                "icfp/microbenchmarks/out/08-Broadcast.out.txt",
                "icfp/microbenchmarks/out/09-HotCRP.out.txt",
                "icfp/microbenchmarks/out/10-AirBnB.out.txt",
                "icfp/microbenchmarks/out/11-Instagram.out.txt"]

CONF_TABLES = ["icfp/conference/out/ConferenceRepair.out.txt", 
               "icfp/conference/out/ConferenceVerification.out.txt"]

GRADR_TABLES = ["icfp/gradr/out/gradr.out.txt"]

HEALTH_TABLES = ["icfp/health/out/HealthWeb.out.txt"]


import re
import os.path

def dictadd(*a):
    d = {}
    for x in a: d.update(x)
    return d

def secs(*b):
    """auxiliary for processing time entries"""
    for el in b:
        assert el.endswith("s")
        yield float(el[:-1])

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


def cmdline():
    import argparse
    a = argparse.ArgumentParser()
    a.add_argument('--seq', action='store_true')
    a.add_argument('filenames')
    return a.parse_args()


if __name__ == '__main__':
    # Micro benchmarks
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

