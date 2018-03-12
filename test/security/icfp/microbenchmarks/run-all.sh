for fn in [1-7]-*.sq; do
  echo $fn
  synquid lifty --print-stats --file=$fn --libs=../Prelude.sq --libs=../Tagged.sq > out/${fn%.sq}.out.txt 2>&1
done
