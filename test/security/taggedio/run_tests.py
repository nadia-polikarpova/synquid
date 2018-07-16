import tempfile
import shutil
import os
import os.path
import subprocess

BASE_DIR = os.path.dirname(__file__)

def in_color(green, text):
  return ("\x1B[01;32m" if green else "\x1B[01;31m") + text + "\x1B[0m"

def run_test(filename, expect_safe):
  proc = subprocess.Popen([
      "synquid", "lifty", "--file="+filename,
      "--libs=TaggedIO.sq", "--libs=Prelude.sq", "--libs=Tagged.sq", "--verify",
    ],
    stdout=subprocess.PIPE,
    stderr=subprocess.PIPE)
  out, err = proc.communicate()
  ret = proc.wait()

  if ret == 0:
    result = "Safe"
  else:
    if ("policy incorrectly depends on another sensitive value" in out):
      result = "Unsafe"
    else:
      result = "Error"

  expected_result = 'Safe' if expect_safe else 'Unsafe'
  is_right = (result == expected_result)
  print in_color(is_right, filename + "    " + ("good" if is_right else "WRONG") + "    (got " + result + ")")


def run_dir(directory, name, expect_safe):
  print name
  for filename in os.listdir(directory):
    if filename.endswith(".sq"):
      run_test(os.path.join(directory, filename), expect_safe)
  print ''

if __name__ == '__main__':
  run_dir(os.path.abspath(os.path.join(BASE_DIR, 'tests/pos')), 'Pos', True)
  run_dir(os.path.abspath(os.path.join(BASE_DIR, 'tests/neg')), 'Neg', False)
