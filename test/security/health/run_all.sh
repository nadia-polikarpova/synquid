mkdir -p out
../../../synquid lifty --libs=../paper/Prelude.sq --libs=../paper/Tagged.sq --file=HealthWeb.sq --print-stats \
    > out/HealthWeb.out.txt 2>&1
