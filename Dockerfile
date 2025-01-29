# Use a Python image with uv pre-installed
FROM ghcr.io/astral-sh/uv:python3.12-bookworm-slim

# Install linux packages
RUN apt-get update && apt-get install -y \
    git \
    make \
    curl \
    gcc \
    bubblewrap \
    libgmp-dev \
    unzip \
    pkg-config \
    build-essential \
    libgmp-dev \
    linux-libc-dev \
    rsync \
    vim \
    && rm -rf /var/lib/apt/lists/*
# N.B. rsync is required for opam pin to a directory

# Install Coq and Lean as early as possible to minimize rebuild frequency
# Install OCaml separately from Coq to allow changing the version of Coq without reinstalling OCaml
# Install the coq-lean-importer late to allow rebuilding it without rebuilding everything else
RUN mkdir -p /root/autoformalization
COPY install/ /root/install
RUN chmod +x /root/install/coq_01_opam_install.sh \
    && /root/install/coq_01_opam_install.sh
RUN chmod +x /root/install/coq_02_coq_install.sh \
    && /root/install/coq_02_coq_install.sh
RUN chmod +x /root/install/lean_install.sh \
    && /root/install/lean_install.sh
RUN chmod +x /root/install/coq_03_lean_import_install.sh \
    && /root/install/coq_03_lean_import_install.sh

# Keep the venv separate from the project directory to stop overwriting the venv when
# the project directory is mounted as a volume
WORKDIR /uv
RUN git config --global --add safe.directory /root/autoformalization

# Copy from the cache instead of linking since it's a mounted volume
ENV UV_LINK_MODE=copy

# Install the project's dependencies using the lockfile and settings
RUN --mount=type=cache,target=/root/.cache/uv \
    --mount=type=bind,source=uv.lock,target=uv.lock \
    --mount=type=bind,source=pyproject.toml,target=pyproject.toml \
    uv sync --frozen --no-install-project

# Place executables in the environment at the front of the path
ENV PATH="/uv/.venv/bin:$PATH"

# Tell uv where the environment is
ENV VIRTUAL_ENV=/uv/.venv
ENV UV_PROJECT_ENVIRONMENT=/uv/.venv

WORKDIR /root/autoformalization

# Infinite loop to keep the container running
ENTRYPOINT ["tail", "-f", "/dev/null"]
