#!/bin/bash
#set -e

cd tests
echo "Profiling ......"
runtest &> /dev/null
cd ..
