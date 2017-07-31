.PHONY: compile
compile:
	dtc -I dts -O dtb linux-tk1-secure.dts >linux-tk1-dtb-secure

.PHONY: decompile
decompile:
	dtc -I dtb -O dts linux-tk1-dtb-secure >linux-tk1-secure.dts
