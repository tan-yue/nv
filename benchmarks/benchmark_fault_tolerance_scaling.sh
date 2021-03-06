#!/usr/bin/env bash

NV="../_build/default/src/exe/main.exe"
BENCHMARKS="
FaultTolerance/SinglePrefix/USCarrierOneLink.nv
FaultTolerance/SinglePrefix/USCarrierTwoLinks.nv
FaultTolerance/SinglePrefix/USCarrierThreeLinks.nv
FaultTolerance/SinglePrefix/fat12polOneLink.nv
FaultTolerance/SinglePrefix/fat12polTwoLinks.nv
FaultTolerance/SinglePrefix/fat12polThreeLinks.nv
FaultTolerance/SinglePrefix/fat16polOneLink.nv
FaultTolerance/SinglePrefix/fat16polTwoLinks.nv
FaultTolerance/SinglePrefix/fat16polThreeLinks.nv
FaultTolerance/SinglePrefix/fat20polOneLink.nv
FaultTolerance/SinglePrefix/fat20polTwoLinks.nv
FaultTolerance/SinglePrefix/fat20polThreeLinks.nv
FaultTolerance/SinglePrefix/fat28polOneLink.nv
FaultTolerance/SinglePrefix/fat28polTwoLinks.nv"

for file in $BENCHMARKS
do
    time "$NV" -inline -compile "$file";
    echo "\n";
done
