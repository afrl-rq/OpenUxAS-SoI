#!/bin/bash
# Copyright © 2017 Government of the United States of America, as represented by the Secretary of the Air Force.
# No copyright is claimed in the United States under Title 17, U. S. Code. All Other Rights Reserved.
# Copyright 2017 University of Cincinnati. All rights reserved. See LICENSE.md file at:
# https://github.com/afrl-rq/OpenUxAS
# Additional copyright may be held by others, as reflected in the commit history.

# from the README.md, 2017-05-08:

echo "Installing dependencies (pdflatex, firefox, sed, evince)..."

# references:
# * http://stackoverflow.com/questions/3466166/how-to-check-if-running-in-cygwin-mac-or-linux/17072017#17072017
# * https://serverfault.com/questions/501230/can-not-seem-to-get-expr-substr-to-work

if [ "$(uname)" == "Darwin" ]; then
#if [ "$($(uname -s) | cut -c 1-6)" == "Darwin" ]; then
    echo " "
    echo "Install basictex (provides pdflatex)..."
    # ref: https://tex.stackexchange.com/questions/307483/setting-up-basictex-homebrew
    brew cask install basictex
    open /usr/local/Caskroom/basictex/*/mactex-basictex-*.pkg
    echo "* In installation window, follow instructions to install basictex"
    echo "  (Continue, Install, etc.)"
    echo "Once you've done this..."
    read -rs -p "Press any key to continue..." -n 1 # reference: https://ss64.com/bash/read.html
    
    echo " "
    # Install firefox, sed, evince (for pdf viewing)
    brew install firefox sed evince
elif [ "$(expr substr $(uname -s) 1 5)" == "Linux" ]; then
    sudo apt update
    # Install texlive-full (provides dflatex), firefox, sed, evince (for pdf viewing)
    sudo apt -y install texlive-full firefox sed evince
else
    echo "This is a Windows platform (Cygwin?) -- unsupported!"
    exit 1
fi

echo "Generating User Manual..."
# run this at: ./OpenUxAS/doc/reference/UserManual
cd ./doc/reference/UserManual
pdflatex UxAS_UserManual.tex

echo "Creating HTML Doxygen reference documentation..."
# run this at: ./OpenUxAS/doc/doxygen
cd ../../doxygen
sh RunDoxygen.sh
echo "Opening ./doc/doxygen/html/index.html in firefox"
firefox ./html/index.html &
echo "Opening ./doc/LMCP/index.html in firefox"
firefox ../LMCP/index.html &

echo "Creating Doxygen PDF reference manual (post-RunDoxygen.sh run)..."
# run this at: ./OpenUxAS/doc/doxygen
cd ./
HOLDSTR=`cat ./ExtraLineToFixLatex.txt`
echo $HOLDSTR
# ref: http://stackoverflow.com/questions/13210880/replace-one-substring-for-another-string-in-shell-script
HOLDSTR2="${HOLDSTR//\\/\\\\}" # need \\ for every \ for sed; "replace every instance" by // instead of /
#echo $HOLDSTR2
sed -i.orig "s/%===== C O N T E N T S =====/${HOLDSTR2}\n%===== C O N T E N T S =====/" ./latex/refman.tex

# run this at: ./OpenUxAS/doc/doxygen/latex
cd ./latex
pdflatex refman.tex
echo "Opening ./doc/doxgen/latex/refman.pdf in evince"
evince refman.pdf &

echo "...Congratulations! You're done with building the documentation!"

# --eof--
