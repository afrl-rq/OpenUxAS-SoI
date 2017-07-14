pushd ..\..\..\OpenAMASE\OpenAMASE
java -Xmx2048m -splash:data\amase_splash.png -cp dist\*;lib\*  avtas.app.Application --config config\amase --scenario "..\..\OpenUxAS\examples\Rendezvous\AMASE_Scenario.xml"
popd

