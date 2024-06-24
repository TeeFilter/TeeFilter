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

# General information (FROM, ARG, LABEL)
# ------------------------------------------------------------------------------
FROM docker.io/ubuntu:focal
LABEL maintainer="joroec@gmx.net"


# Build time arguments (ARG)
# ------------------------------------------------------------------------------

ARG USER_ID
ARG GROUP_ID


# Runtime arguments (ENV)
# ------------------------------------------------------------------------------

ENV USER_ID=$USER_ID
ENV GROUP_ID=$GROUP_ID


ENV DEBIAN_FRONTEND=noninteractive

ENV LANG en_US.UTF-8
ENV LANGUAGE en_US:en
ENV LC_ALL en_US.UTF-8

ENV PATH=/home/user/.local/bin:$PATH


# Image setup (ADD, RUN, COPY, WORKDIR, ONBUILD)
# ------------------------------------------------------------------------------

# Set the locale
RUN /bin/sh -c 'apt-get update \
    && apt-get install -y --no-install-recommends locales \
    && sed -i -e "s/# en_US.UTF-8 UTF-8/en_US.UTF-8 UTF-8/" /etc/locale.gen \
    && locale-gen \
    && rm -rf /var/lib/apt/lists/* \
    && rm -rf /etc/localtime \
    && ln -s /usr/share/zoneinfo/Europe/Berlin /etc/localtime'

# Add an user with sudo access
RUN /bin/sh -c 'apt-get update \
    && apt-get install -y --no-install-recommends \
      sudo \
    && rm -rf /var/lib/apt/lists/*'
RUN /bin/sh -c 'addgroup --gid $GROUP_ID user \
  && adduser --uid $USER_ID --home "/home/user" --gid $GROUP_ID \
    --shell "/bin/bash" --disabled-password --gecos "" user \
  && adduser user sudo \
  && echo "%sudo ALL=(ALL) NOPASSWD:ALL" >> /etc/sudoers'

# General system dependencies
# Taken from https://buildroot.org/downloads/manual/manual.html#requirement-mandatory
RUN /bin/sh -c 'apt-get update \
    && apt-get install -y --no-install-recommends \
      debianutils sed make build-essential binutils gcc g++ bash patch gzip bzip2 perl tar cpio unzip rsync file bc openssh-client \
      wget python3 \
      bzr cvs git mercurial subversion \
      libncurses5 libncurses5-dev asciidoc-base w3m \
      less vim nano \
      libssl-dev \
      clang llvm libc6-dev-i386 \
    && rm -rf /var/lib/apt/lists/*'

# Privilege drop
USER $USER_ID:$GROUP_ID
WORKDIR /home/user

# Copy the entrypoint script to the image
COPY ./entrypoint.sh /usr/local/bin/entrypoint.sh


# Volume setup (VOLUME)
# ------------------------------------------------------------------------------


# Runtime setup (ENTRYPOINT, CMD, SHELL, EXPOSE, USER, STOPSIGNAL, HEALTCHECK)
# ------------------------------------------------------------------------------

ENTRYPOINT [ "/usr/local/bin/entrypoint.sh" ]
CMD [ "/bin/bash" ]
