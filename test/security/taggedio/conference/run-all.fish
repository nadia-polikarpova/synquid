for fn in Conference{Verification,Repair}.sq
    echo $fn
    synquid lifty --print-stats --file=$fn --libs=../Prelude.sq --libs=../Tagged.sq --libs=Conference.sq > out/$fn.out 2>&1
  end
  