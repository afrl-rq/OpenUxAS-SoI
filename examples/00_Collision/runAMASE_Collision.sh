here=$PWD;

cd ../../../OpenAMASE/OpenAMASE;
java -Xmx2048m -splash:./data/amase_splash.png -classpath ./dist/*:./lib/*  avtas.app.Application --config config/amase_headless --simrate = 1.0 --scenario "../../OpenUxAS/examples/00_Collision/MessagesToSend/collision.xml";
cd "$here";

