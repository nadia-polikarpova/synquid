python3 gen.py
mkdir -p out
synquid lifty --libs=../Tagged.sq --libs=../Prelude.sq \
    --file=OneFunc.sq --print-stats \
    > out/OneFunc.out.txt 2>&1
