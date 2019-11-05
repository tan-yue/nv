#!/usr/bin/env bash

NV="../_build/default/src/exe/main.exe"
BENCHMARKS="FaultTolerance/SinglePrefix/USCarrierOneLink.nv
FaultTolerance/SinglePrefix/USCarrierTwoLinks.nv
FaultTolerance/SinglePrefix/USCarrierFourLinks.nv
FaultTolerance/SinglePrefix/fat12polOneLink.nv
FaultTolerance/SinglePrefix/fat12polTwoLinks.nv
FaultTolerance/SinglePrefix/fat12polFourLinks.nv
FaultTolerance/SinglePrefix/fat16polOneLink.nv
FaultTolerance/SinglePrefix/fat16polTwoLinks.nv
FaultTolerance/SinglePrefix/fat16polFourLinks.nv
FaultTolerance/SinglePrefix/fat20polOneLink.nv
FaultTolerance/SinglePrefix/fat20polTwoLinks.nv
FaultTolerance/SinglePrefix/fat20polFourLinks.nv"

for file in $BENCHMARKS
do
    time "$NV" -inline -compile "$file";
    echo "\n";
done