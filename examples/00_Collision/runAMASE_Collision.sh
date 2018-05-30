#save the current directory
SAVE_DIR=$(pwd)

#location of OpenAMASE
BIN2="../../../OpenAMASE/OpenAMASE"
# run OpenAMASE in separate terminal.  Note: requires "gnome-terminal"
cd $BIN2
#/usr/bin/gnome-terminal -x java -Xmx2048m -splash:./data/amase_splash.png -classpath ./dist/*:./lib/*  avtas.app.Application --config config/amase --scenario "../../OpenUxAS/examples/00_Collision/MessagesToSend/collision_mkii.xml"; 
/usr/bin/gnome-terminal -x java -Xmx2048m -splash:./data/amase_splash.png -classpath ./dist/*:./lib/*  avtas.app.Application --config config/daidalus --scenario "../../OpenUxAS/examples/00_Collision/MessagesToSend/collision_mkii.xml"; 
# change back to original directory
cd $SAVE_DIR
