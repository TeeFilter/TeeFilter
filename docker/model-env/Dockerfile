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
FROM diffblue/cbmc:5.87.0
LABEL maintainer="jonas.roeckl@fau.de"


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

# General system dependencies
RUN /bin/sh -c 'apt-get update \
    && apt-get install -y --no-install-recommends \
      make build-essential binutils gcc \
      gcc-aarch64-linux-gnu binutils-aarch64-linux-gnu libc6-dev-arm64-cross \
      python3 \
    && rm -rf /var/lib/apt/lists/*'

# z3 SMT solver so that we can run cbmc with '--z3' (fails silently otherwise)
RUN /bin/sh -c 'apt-get update \
    && apt-get install -y --no-install-recommends \
      z3 \
    && rm -rf /var/lib/apt/lists/*'

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
