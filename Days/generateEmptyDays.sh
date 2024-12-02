#!/usr/bin/env bash

for i in {1..25}; do
  dayFile="Day$i.lean"
  if [ ! -f $dayFile ]; then
    cp ./DayN.template $dayFile
    sed -i "s/DayN/Day$i/" $dayFile
  fi
done
