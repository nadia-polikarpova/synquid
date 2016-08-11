for fn in Conference{Verification,Repair}.sq ; do
  echo $fn
  ../../../dist/build/synquid/synquid lifty --print-stats $fn ../paper/Security.sq Conference.sq -l 1 > out/${fn%.sq}.out.txt 2>&1
done
