pushd ..\..\..\OpenAMASE\OpenAMASE
java -Xmx2048m -cp dist\*;lib\*  avtas.app.Application --config config\amase_headless --scenario "..\..\OpenUxAS\examples\06_Test_WaterwaySearch\Scenario_WaterwaySearch.xml"
popd


