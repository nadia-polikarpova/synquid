import re


ONEFUNC = r"""
oneFunc%(n)d :: World -> World
oneFunc%(n)d = \w.
  let u = getSessionUser w in
  %(vlets)s
  let v = %(listexpr)s
  in
     print w u (liftM show v)
"""

VLET = r"""
  let v%(i)d = getPrivateValue w in
"""

LISTBIND = r"""bind v%(i)d (\b%(i)d. %(inner)s)"""

INSERT_RE = re.compile(r"(----  AUTOGEN.*?\n).*?(\n----)", re.DOTALL)


def mk_vlets(n):
    return ''.join(VLET % {'i': i} for i in range(n))

def mk_listexpr(n):
    e = "return [%s]" % ", ".join("b%d" % i for i in range(n))

    for i in range(n):
        e = LISTBIND % {'i': i, 'inner': e}

    return e

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

