mkdir -p out
synquid lifty --file=Stuff.sq --libs=TaggedIO.sq --libs=Prelude.sq --libs=Tagged.sq --print-stats  --verify #\
    #> out/HealthWeb.out.txt 2>&1
