here=$PWD;

cd ../../../OpenAMASE/OpenAMASE;
java -Xmx2048m -classpath ./dist/*:./lib/*  avtas.app.Application --config config/amase_headless --sim_rate 5.0 --scenario "../../OpenUxAS/examples/06_Test_WaterwaySearch/Scenario_WaterwaySearch.xml";
cd "$here";

