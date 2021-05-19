#!/bin/bash

make

EXIT_SUCCESS=0

for file in ./good/*
do
    echo "${file}"
    ./interpreter "${file}" || EXIT_SUCCESS=$?
done

echo $EXIT_SUCCESS
exit $EXIT_SUCCESS