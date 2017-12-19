.PHONY: all clean clean2 spark lib combo z3 cvc4 altergo cvc3 check pvs

all: spark lib

num_proc=7
proj_name=waypoint_manager
src_dir=src
build_dir=build
proof_dir=proof
spark_dir=${build_dir}/spark
lib_dir=library
driver_prefix=waypoint_manager
driver_file=${driver_prefix}.adb
sum_file=${driver_prefix}.sum
srcs=${src_dir}/*.ad?
timeout=100
shortto=10
cvc4opts=--level=4
z3opts=--level=4
altergoopts=--level=4

qz3: 
	gnatprove -P${proj_name}.gpr -U -j${num_proc} --prover=z3 --timeout=${shortto}

qcvc4:
	gnatprove -P${proj_name}.gpr -U -j${num_proc} --prover=cvc4 --timeout=${shortto}

z3: 
	gnatprove -P${proj_name}.gpr -U -j${num_proc} --prover=z3 --timeout=${timeout} --no-counterexample ${z3opts}

cvc4: 
	gnatprove -P${proj_name}.gpr -U -j${num_proc} --prover=cvc4 --timeout=${timeout} ${cvc4opts}

# Explanation of combo:
# 1. The output of gnatprove will match ":[0-9]\+:" iff there are undischarged VCs
# 2. We use `tee /dev/tty` so that we can see the output of the make commands while also piping them to grep
# 3. We redirect the output of grep to /dev/null so that undischarged VCs aren't duplicated (see #2)
# 4. Grep returns an error if there is no match, so a grep error means all VCs are discharged (i.e., a grep error is good!)
# 5. Leading - means to ignore errors (see #4)
combo:
	pwd
	-(make qz3 | tee /dev/tty | grep ":[0-9]\+:" > /dev/null && make cvc4 | tee /dev/tty | grep ":[0-9]\+:" > /dev/null && make z3 | tee /dev/tty | grep ":[0-9]\+:" > /dev/null && make altergo)

altergo: 
	gnatprove -P${proj_name}.gpr -U -j${num_proc} --prover=altergo --timeout=${timeout} --no-counterexample ${altergoopts} 

cvc3: 
	gnatprove -P${proj_name}.gpr -U -j${num_proc} --prover=cvc3 --timeout=${timeout} 

pvs: 
	gnatprove -P${proj_name}.gpr -U -j${num_proc} --prover=pvs

clean:
	rm -rf *~ ${build_dir} ${proof_dir} ${lib_dir} ${sum_file} ${src_dir}/${proj_name}.{sli,lst,smf,idx} ${src_dir}/${driver_prefix}.{sli,lst,smf,idx} ${src_dir}/spark.rep ${src_dir}/${driver_prefix} ${src_dir}/*~ ${src_dir}/.#*#
	mkdir ${build_dir}
	mkdir ${lib_dir}

clean2:
	rm -rf build/gnatprove/${driver_prefix}*

spark:
	time make combo

baseline:
	gnatprove -P${proj_name}.gpr --level=2 -j${num_proc}

timedbaseline:
	{ time make baseline ; } 2>&1 | tee /dev/tty > timedbaseline.txt

check:
	@gnatprove -P${proj_name}.gpr -U -j${num_proc} --prover=cvc4 --steps=1 | grep ":[0-9]\+:" && echo "Undischarged VCs in `pwd`" || echo "All VCs discharged in `pwd`"

lib: ${srcs} ${proj_name}.gpr ${src_dir}/${proj_name}.cfg
	gprbuild -d -P${proj_name}.gpr -s -j${num_proc} -p

