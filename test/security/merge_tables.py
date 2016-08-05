
CONF_METAPROGRAM = {
  'columns':         ["braces(key)", "$1", "#2'-#1", "#2-#1", "$3'", "$3", "$4", "$5", "$6"],
  'rows': ["test1",
           "test2",
           "test3",
           "test4",
           "test5",
           "test6",
           "selectFrom",
           "test7",
           "test8",
           "test9",
           "test10",
           "test11",
           "test12",
           "Totals"],
  'fmt': ["\\d%-20s", "%s", "%8s", "%8s", "%s", "%s", "%s", "%s", "%s"],
  'helpers': {
    'braces': (lambda txt: "{%s}" % txt)
  }
}

MICRO_METAPROGRAM = {
  'columns':         ["micro(key)", "$3", "$4", "$5", "$6"],
  'rows': ["1-Basic.out:showPaper",
           "2-SelfRef.out:showPaper",
           "3-Implicit.out:showSession",
           "4-Search.out:searchByAuthor",
           "5-Sort.out:sortPapersByScore",
           "6-Multicast.out:notifyAuthors"],
  'fmt': ["\\d%-20s", "%s", "%s", "%s", "%s"],
  'helpers': {
    'micro': (lambda txt: "{micro%s}" % txt.split('-')[0])
  }
}

CONF_TABLES = ["conference/out/ConferenceRepair.out.txt", 
               "conference/out/ConferenceVerification.out.txt"]
MICRO_TABLES = ["paper/out/1-Basic.out.txt", 
                "paper/out/2-SelfRef.out.txt", 
                "paper/out/3-Implicit.out.txt", 
                "paper/out/4-Search.out.txt", 
                "paper/out/5-Sort.out.txt", 
                "paper/out/6-Multicast.out.txt"]

import re
import os.path

def dictadd(*a):
    d = {}
    for x in a: d.update(x)
    return d


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
    return eval(expr, dictadd({'_': value, 'key': key}, helpers))


class Program(object):
    
    def __init__(self, metaprogram):
        self.metaprogram = metaprogram

    def eval_meta(self, tables):
        out = []
        for rowh in self.metaprogram['rows']:
            row = [table[rowh] for table in tables]
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
    ctx = [parse_table(fn) for fn in CONF_TABLES]  # "in parallel"
    mp = Program(CONF_METAPROGRAM)
    mp.fmt_output( mp.eval_meta(ctx) )
    ctx = [concat_tables(parse_table(fn) for fn in MICRO_TABLES)]  # "in sequence"
    mp = Program(MICRO_METAPROGRAM)
    mp.fmt_output( mp.eval_meta(ctx) )
