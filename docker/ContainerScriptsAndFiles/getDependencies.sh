#!/bin/bash


# NAME
#	GetDependencies.sh  - exports the bare essentials for a executable file for a Docker image
#
# SYNOPSIS
#	GetDependencies.sh  executableFile
#
#
# # DESCRIPTION
#   this script copies all the all shared libraries required by the executable to a given directory
#
# # CAVEATS
#	requires an image that has a bash, readlink and ldd  installed.



# BASED ON:
# "strip-docker-image-export"
# https://github.com/mvanholsteijn/strip-docker-image
# AUTHOR
#  Mark van Holsteijn
#
# COPYRIGHT
#
#   Copyright 2015 Xebia Nederland B.V.
#
#   Licensed under the Apache License, Version 2.0 (the "License");
#   you may not use this file except in compliance with the License.
#   You may obtain a copy of the License at
#
#       http://www.apache.org/licenses/LICENSE-2.0
#
#   Unless required by applicable law or agreed to in writing, software
#   distributed under the License is distributed on an "AS IS" BASIS,
#   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#   See the License for the specific language governing permissions and
#   limitations under the License.
#



FILE=$1
EXPORT_DIR=$2
#VERBOSE=v

function print_file() {
		if [ "$1" = "/usr/bin/ldd" ]; then
			exit
		fi

		if [ -e "$1" ] ; then
			echo "$1"
		else
			test -n "$VERBOSE" && echo "INFO: ignoring not existent file '$1'" >&2
		fi

		if [ -s "$1" ] ; then
			TARGET=$(readlink "$1")
			if  [ -n "$TARGET" ] ; then
				if expr "$TARGET" : '^/' >/dev/null 2>&1 ; then
					#list_dependencies "$TARGET"
					test -n "$VERBOSE" && echo "INFO: link target '$TARGET'" >&2
					if [ -e "$TARGET" ] ; then
						echo "$TARGET"
					else
						test -n "$VERBOSE" && echo "INFO: ignoring not existent file '$TARGET'" >&2
					fi
				else
					#list_dependencies $(dirname "$1")/"$TARGET"
					test -n "$VERBOSE" && echo "INFO: including "$(dirname "$1")"/"$TARGET >&2
					test -n "$VERBOSE" && echo "INFO: link target '$TARGET'" >&2
					if [ -e $(dirname "$1")/"$TARGET" ] ; then
						echo $(dirname "$1")/"$TARGET"
					else
						test -n "$VERBOSE" && echo "INFO: ignoring not existent file '$TARGET'" >&2
					fi
				fi
			fi
		fi
}

function list_dependencies() {
	FILE=$@
		if [ -e "$FILE" ] ; then
			#print_file "$FILE"
			if /usr/bin/ldd "$FILE" >/dev/null 2>&1 ; then
				#/usr/bin/ldd "$FILE">&2
				/usr/bin/ldd "$FILE" | \
				awk '/statically/{next;} /=>/ { print $3; next; } { print $1 }' | \
				while read LINE ; do
					test -n "$VERBOSE" && echo "INFO: including $LINE" >&2
					print_file "$LINE"
				done
			fi
		else
			test -n "$VERBOSE" && echo "INFO: ignoring not existent file $FILE" >&2
		fi
}

test -n "$VERBOSE" && echo "INFO: removing old export directory '$EXPORT_DIR'" >&2
rm -rf $EXPORT_DIR
mkdir -p ${EXPORT_DIR}

test -n "$VERBOSE" && echo "INFO: finding and saving dependencies" >&2
tar cf - $(( list_dependencies $FILE ) | sort -u ) | (cd $EXPORT_DIR ; tar -x${VERBOSE}f - )
cp $FILE $EXPORT_DIR


