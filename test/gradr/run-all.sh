mkdir -p out
synquid lifty --print-stats --file=gradr.sq --libs=../Prelude.sq --libs=../Tagged.sq --libs=models.sq \
    > out/gradr.out.txt 2>&1
