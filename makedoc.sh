#/bin/bash
SOURCES=`grep .v Make`
echo ${SOURCES}
rm -rf ../doc/html/*
mkdir ../doc/html
# --coqlib_path "`coqc -where`"
coqdoc --utf8 -R . FingerTree --interpolate --multi-index -g -l -t "Finger Trees" --toc -d ../doc/html --html ${SOURCES} 
