#!/bin/bash

################################################################################

# Copyright (C) 2022-2024 Jonas Röckl <joroec@gmx.net>
# This program is free software; you can redistribute it and/or
# modify it under the terms of the GNU General Public License
# as published by the Free Software Foundation; either version 2
# of the License, or (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; If not, see <http://www.gnu.org/licenses/>.

################################################################################

# Exit immediately and do not process any further if one of the following
# commands fail.
set -e

# Extract the directory of this script and its exact name, so that this script
# can be called from anywhere.
DIR="$( cd "$( dirname "$0" )" && pwd )"
FILE="$( basename "$0" )"
echo "Running the script '$DIR/$FILE'"
cd $DIR/../..

################################################################################

NAME="teefilter-build-env"
TAG="latest"

REPO_DIR="$( pwd )"

# allow to call the script interactively
if [ "$#" -eq 2 ] && [[ "$1" == '-c' ]] ; then
  CMD=$2
else
  CMD="/bin/bash"
fi

docker run -it --rm \
  --name teefilter-build-env \
  --volume $REPO_DIR:/home/user/teefilter \
  --group-add=sudo \
  $NAME:$TAG \
  "cd /home/user/teefilter/ && $CMD"
