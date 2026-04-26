#!/bin/bash
for arg1 in 30000 60000 90000; do
    stack run evaluate-exe $arg1
done