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
    && rm -rf /var/lib/apt/lists/*

# Install Coq and Lean as early as possible to minimize rebuild frequency
COPY coq_install.sh /root/coq_install.sh
COPY lean_install.sh /root/lean_install.sh
RUN chmod +x /root/coq_install.sh \
    && /root/coq_install.sh \
    && chmod +x /root/lean_install.sh \
&& /root/lean_install.sh

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
