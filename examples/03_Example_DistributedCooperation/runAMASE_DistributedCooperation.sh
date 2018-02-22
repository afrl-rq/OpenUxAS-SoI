here=$PWD;

cd ../../../OpenAMASE/OpenAMASE;
java -Xmx2048m -splash:./data/amase_splash.png -classpath ./dist/*:./lib/*  avtas.app.Application --config config/amase_headless --sim_rate 1.0 --scenario "../../OpenUxAS/examples/03_Example_DistributedCooperation/Scenario_DistributedCooperation.xml";
cd "$here";

