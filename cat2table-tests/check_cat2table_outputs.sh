cat2table7 -e1 "Exp&W" -e2 "Imp&TTD&R" > "actual-outputs/Exp&W+Imp&TTD&R.txt"
cat2table7 -e1 "W" -e2 "Imp&TTD&R" > "actual-outputs/W+Imp&TTD&R.txt"
cat2table7 -e1 "TLBI" -e2 "W" > "actual-outputs/TLBI+W.txt"
cat2table7 -e1 "TLBI" -e2 "Imp&TTD&R" > "actual-outputs/TLBI+Imp&TTD&R.txt"
cat2table7 -e1 "Imp&TTD&R" -e2 "Exp&W" > "actual-outputs/Imp&TTD&R+Exp&W.txt"
cat2table7 -e1 "Imp&TTD&R" -e2 "W" > "actual-outputs/Imp&TTD&R+W.txt"
cat2table7 -e1 "Imp&Tag&R" -e2 "Exp&W" > "actual-outputs/Imp&Tag&R+Exp&W.txt"
cat2table7 -e1 "Imp&TTD" -e2 "Imp&TTD" > "actual-outputs/Imp&TTD+Imp&TTD.txt"
#!/bin/sh

fail=0

git diff --no-index --quiet ./actual-outputs/Exp\&W+Imp\&TTD\&R.txt \
  ./expected-outputs/Exp\&W+Imp\&TTD\&R.txt \
  || { echo "Diff detected for Exp&W+Imp&TTD&R"; fail=1; }

git diff --no-index --quiet ./actual-outputs/W+Imp\&TTD\&R.txt \
  ./expected-outputs/W+Imp\&TTD\&R.txt \
  || { echo "Diff detected for W+Imp&TTD&R"; fail=1; }

git diff --no-index --quiet ./actual-outputs/TLBI+W.txt \
  ./expected-outputs/TLBI+W.txt \
  || { echo "Diff detected for TLBI+W"; fail=1; }

git diff --no-index --quiet ./actual-outputs/TLBI+Imp\&TTD\&R.txt \
  ./expected-outputs/TLBI+Imp\&TTD\&R.txt \
  || { echo "Diff detected for TLBI+Imp&TTD&R"; fail=1; }

git diff --no-index --quiet ./actual-outputs/"Imp&TTD&R+Exp&W.txt" \
  ./expected-outputs/"Imp&TTD&R+Exp&W.txt" \
  || { echo "Diff detected for Imp&TTD&R+Exp&W"; fail=1; }

git diff --no-index --quiet ./actual-outputs/"Imp&TTD&R+W.txt" \
  ./expected-outputs/"Imp&TTD&R+W.txt" \
  || { echo "Diff detected for Imp&TTD&R+W"; fail=1; }

git diff --no-index --quiet ./actual-outputs/"Imp&Tag&R+Exp&W.txt" \
  ./expected-outputs/"Imp&Tag&R+Exp&W.txt" \
  || { echo "Diff detected for Imp&Tag&R+Exp&W"; fail=1; }

git diff --no-index --quiet ./actual-outputs/Imp\&TTD+Imp\&TTD.txt \
  ./expected-outputs/Imp\&TTD+Imp\&TTD.txt \
  || { echo "Diff detected for Imp&TTD+Imp&TTD"; fail=1; }

if [ "$fail" -ne 0 ]; then
  exit 1
fi

echo "All good!"