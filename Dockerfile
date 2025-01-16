# Use a Python image with uv pre-installed
FROM ghcr.io/astral-sh/uv:python3.12-bookworm-slim

# Install linux packages
RUN apt-get update && apt-get install -y \
    git \
    make \
    && rm -rf /var/lib/apt/lists/*

# Keep the venv separate from the project directory to stop overwriting the venv when
# the project directory is mounted as a volume
WORKDIR /uv

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

RUN git config --global --add safe.directory /root/autoformalization

WORKDIR /root/autoformalization

# Infinite loop to keep the container running
ENTRYPOINT ["tail", "-f", "/dev/null"]
