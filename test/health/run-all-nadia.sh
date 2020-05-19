mkdir -p out
synquid lifty --libs=../Prelude.sq --libs=../Tagged.sq --file=HealthWeb.sq --print-stats \
    > out/HealthWeb.out.txt 2>&1
