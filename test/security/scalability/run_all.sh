python3 gen.py
mkdir -p out
../../../synquid lifty --libs=../paperWrites/Tagged.sq --libs=../paperWrites/Prelude.sq \
    --file=OneFunc.sq --print-stats \
    > out/OneFunc.out.txt 2>&1
