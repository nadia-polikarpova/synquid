for fn in [1-7]-*.sq; do
  echo $fn
  Synquid.exe lifty --print-stats $fn Prelude.sq Tagged.sq -l 1 > out/${fn%.sq}.out.txt 2>&1
done
