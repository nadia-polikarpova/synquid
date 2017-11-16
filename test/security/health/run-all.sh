mkdir -p out
../../../synquid lifty --libs=../paperWrites/Prelude.sq --libs=../paperWrites/Tagged.sq --file=HealthWeb.sq --print-stats \
    > out/HealthWeb.out.txt 2>&1
