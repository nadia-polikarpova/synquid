for fn in [1-6]-*.sq; do
  echo $fn
  ../../../dist/build/synquid/synquid lifty --print-stats $fn Prelude.sq Tagged.sq -l 1 > out/${fn%.sq}.out.txt 2>&1
done
