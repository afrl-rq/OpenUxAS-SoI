here=$PWD;

cd ../../../../OpenAMASE/OpenAMASE;
java -Xmx2048m -splash:./data/amase_splash.png -classpath ./dist/*:./lib/*  avtas.app.Application --config config/amase --scenario "../../OpenUxAS/examples/tasks/BlockadeTask/Scenario_BlockadeTask.xml";
cd "$here";

