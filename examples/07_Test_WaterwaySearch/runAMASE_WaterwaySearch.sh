here=$PWD;

cd ../../../OpenAMASE/OpenAMASE;
java -Dname=Amase -Xmx2048m -splash:./data/amase_splash.png -classpath ./dist/*:./lib/*  avtas.app.Application --config config/amase --scenario "../../OpenUxAS/examples/07_Test_WaterwaySearch/Scenario_WaterwaySearch.xml";
cd "$here";

