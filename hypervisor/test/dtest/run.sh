#!/bin/bash
if [[ "$1" == *"--debug"* ]]
then
~/qemu/bin/qemu-system-arm -M beaglexm -m 512 -sd ../../../sth_deps/beagle_sd_working.img -nographic -s -S
else
~/qemu/bin/qemu-system-arm -M beaglexm -m 512 -sd ../../../sth_deps/beagle_sd_working.img -nographic
fi
