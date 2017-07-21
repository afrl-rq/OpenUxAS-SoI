here=$PWD;

cd ../../../OpenAMASE/OpenAMASE;
java -Xmx2048m -classpath ./dist/*:./lib/*  avtas.app.Application --config config/amase --scenario "../../OpenUxAS/examples/02_Example_WaterwaySearch/Scenario_WaterwaySearch.xml";
cd "$here";

