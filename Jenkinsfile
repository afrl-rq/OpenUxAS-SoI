// this is a Jenkinsfile designed specifically to work with internal
// Galois infrastructure, so it makes some internal assumptions. Maybe
// it should be made more broad at some point, but it works for now
pipeline {
    // most of our build machines don't have docker, so this label
    // restricts it to build machines that do
    agent { label 'uxas' }

    stages {
        // first get rid of the old artifacts
        stage('Cleaning') {
            steps {
                sh 'docker run -v $(pwd):/opt:z debian rm -rf /opt/LmcpGen /opt/OpenUxAS'
                sh 'docker rm -f $(docker ps -a -q) || true'
                sh 'docker rmi -f $(docker images -a -q) || true'
            }
        }

        // then fetch the appropriate branches on the appropriate
        // repos
        stage('Fetching') {
            steps {
                sh 'git clone -b buildroot-docker-rust https://github.com/GaloisInc/OpenUxAS.git'
                sh 'git clone -b develop https://github.com/GaloisInc/LmcpGen.git'
            }
        }

        // finally, start the two-stage build process:
        stage('Building') {
            steps {
                // first generating the lmcp bindings
                dir('LmcpGen') {
                    sh 'ant jar'
                }

                // then preparing and installing the uxas stuff
                dir('OpenUxAS') {
                    sh './RunLmcpGen.sh'
                    sh './prepare'
                    sh './docker/build_sdcard_and_uxas.sh'
                }
            }
        }

        // this uploads the final artifacts to our internal
        // Artifactory instance
        stage('Uploading') {
            steps {
                script{
                    // Obtain our local Artifactory server instances
                    def server = Artifactory.server "artifactory.galois.com"

                    def uploadSpec = """{ "files": [
                      { "pattern": "OpenUxAS/build_cross/uxas", "target": "galwegians_generic-local" },
                      { "pattern": "OpenUxAS/sdcard.img", "target": "galwegians_generic-local" }
                    ]}"""

                    def buildInfo = server.upload spec: uploadSpec

                    // Publish the build-info to Artifactory
                    server.publishBuildInfo buildInfo
                }
            }
        }
    }
}
