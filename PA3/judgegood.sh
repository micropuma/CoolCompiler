#!/bin/bash

filename = good.cl  
echo "testing ------- good.cl ------------"
./refparser $filename > refout 2> referr
./myparser $filename > myout 2> myerr

if diff myout refout; then
    if diff myerr referr; then
        echo "passed"
    else
        echo "failed"
    fi
else 
    echo "failed"
fi

rm -rf refout myout myerr referr myerr_sorted referr_sorted



