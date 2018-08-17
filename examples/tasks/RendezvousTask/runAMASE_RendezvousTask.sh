here=$PWD;

cd ../../../../OpenAMASE/OpenAMASE;
java -Xmx2048m -splash:./data/amase_splash.png -classpath ./dist/*:./lib/*  avtas.app.Application --config config/amase --scenario "../../OpenUxAS/examples/tasks/RendezvousTask/Scenario_RendezvousTask.xml";
cd "$here";

