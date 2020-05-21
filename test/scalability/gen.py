import re


ONEFUNC = r"""
oneFunc%(n)d :: Store -> User -> TIO Unit <{False}> <{True}>
oneFunc%(n)d = \ds . \client .
  do%(vlets)s
    print client (show %(listexpr)s)
"""

VLET = r"""
    v%(i)d <- getPrivateValue ds
"""

INSERT_RE = re.compile(r"(----  AUTOGEN.*?\n).*?(\n----)", re.DOTALL)


def mk_vlets(n):
    return ''.join(VLET % {'i': i} for i in range(n))

def mk_listexpr(n):
    return "[%s]" % ", ".join("v%d" % i for i in range(n))

def mk_oneFunc(n):
    return (ONEFUNC % {'n': n, 'vlets': mk_vlets(n), 'listexpr': mk_listexpr(n)})\
            .replace('\n\n', '\n')


def mk_oneFuncs(n):
    return ''.join(mk_oneFunc(i+1) for i in range(n))



if __name__ == '__main__':
    fn = "OneFunc.sq"
    n = 16

    txt = open(fn).read()
    insert = mk_oneFuncs(n)
    txt = INSERT_RE.sub(lambda mo: mo.group(1) + insert + mo.group(2), txt)

    with open(fn, 'w') as outf:
        outf.write(txt)

