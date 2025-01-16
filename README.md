## Develop Python in Docker

*Note: These instructions generally assume you're working in a Unix shell (bash, zsh etc.)*

This setup is broadly inspired by [https://github.com/astral-sh/uv-docker-example](https://github.com/astral-sh/uv-docker-example).

### Why

- Consistent environment across machines - i.e. no worrying about installing dependencies, stuff running my machine and not on yours/in the cloud.

### Prerequisites

1. Install Docker, probably through [docker desktop](https://docs.docker.com/desktop/setup/install/linux/ubuntu/) or [docker engine](https://docs.docker.com/engine/install/ubuntu/).
    - Verify it's installed by running `docker --version`

1. If you haven't installed Docker Desktop, install the [Docker Compose plugin](https://docs.docker.com/compose/install/linux/#install-using-the-repository)
    - Verify it's installed by running `docker compose version`

1. If using VSCode or Cursor, install the following extensions:
    - [Dev Containers](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-containers)
    - [Docker](https://marketplace.visualstudio.com/items?itemName=ms-azuretools.vscode-docker)

### Steps

1. Clone the repo and `cd` into it.
1. Run `docker compose up -d`
    - Note: If you change anything in the `Dockerfile`, you may need to run `docker-compose up -d --build` to see the changes reflected in the container.
1. Open the Docker extension in your toolbar, you should see a running container called `autoformalization-autoformalization` running.
1. Right click it and select 'Attach Visual Studio Code'. This should open up a new VSCode Window inside the container.
1. Any changes you make to files within the `/autoformalization` directory within the container should be reflected in the `autoformalization` directory on your machine.

To stop the container, you can run `docker compose down`.

### Adding Python dependencies

1. Run `uv add <package-name>`
1. Make sure you commit the changed `uv.lock` and `pyproject.toml` files to Git.

## Running Pre-Commit

This will lint and format your code.

1. To manually run pre-commit, simply run `pre-commit`.
1. To avoid having to manually run, you can set it to automatically run every time you run `git commit` by running `pre-commit install`.

### About UV

UV is a super fast Python dependency manager. It manages Python dependencies, build dependencies, Python versions and probably more. It's probably best described as a better version of poetry. It's nice because it's:

1. Really fast.
1. Maintains a lock file.

Read more about it [here](https://docs.astral.sh/uv/).