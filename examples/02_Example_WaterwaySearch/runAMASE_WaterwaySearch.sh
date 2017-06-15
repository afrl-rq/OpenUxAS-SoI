here=$PWD;

cd ../../../OpenAMASE/OpenAMASE;
java -classpath ./dist/*:./lib/*  avtas.app.Application --config config/amase_headless --scenario "../../OpenUxAS/examples/02_Example_WaterwaySearch/Scenario_WaterwaySearch.xml"; #--sim_rate 1 
cd "$here";

