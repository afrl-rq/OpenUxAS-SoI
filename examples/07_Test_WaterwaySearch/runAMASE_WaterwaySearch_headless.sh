here=$PWD;

cd ../../../OpenAMASE/OpenAMASE;
java -Dname=Amase -Xmx2048m -classpath ./dist/*:./lib/*  avtas.app.Application --config config/amase_headless --sim_rate 25.0 --scenario "../../OpenUxAS/examples/06_Test_WaterwaySearch/Scenario_WaterwaySearch.xml";
cd "$here";

