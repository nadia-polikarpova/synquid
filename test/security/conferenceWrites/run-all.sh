for fn in Conference{Verification,Repair}.sq ; do
  echo $fn
  ../../../synquid lifty --print-stats --file=$fn --libs=../paperWrites/Prelude.sq --libs=../paperWrites/Tagged.sq --libs=Conference.sq > out/${fn%.sq}.out.txt 2>&1
done
