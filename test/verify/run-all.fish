echo Prelude
synquid lifty --print-stats --verify --file=../Prelude.sq > out/Prelude.out 2>&1

echo Tagged
synquid lifty --print-stats --verify --file=../Tagged.sq --libs=../Prelude.sq > out/Tagged.out 2>&1

for fn in ok1 ok2 ok3 ok4 bad1 bad2 bad3 bad4
    echo $fn
    synquid lifty --print-stats --verify --only=$fn --file=Test.sq --libs=../Prelude.sq --libs=../Tagged.sq > out/$fn.out 2>&1
  end  

for fn in *.sq
    if test "$fn" != "Test.sq"
      echo $fn
      synquid lifty --print-stats --verify --file=$fn --libs=../Prelude.sq --libs=../Tagged.sq > out/$fn.out 2>&1
    end
  end