for fn in *.sq
    echo $fn
    synquid lifty --print-stats --file=$fn --libs=../Prelude.sq --libs=../Tagged.sq > out/$fn.out 2>&1
  end