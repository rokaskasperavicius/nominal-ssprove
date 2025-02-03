# Nominal-SSProve

Install dependencies by entering the nix-shell with command `nix-shell` or using the docker environment as described below.

Check all project files using `make` and inspect files using vim (with Coqtail).

## Docker environment

Build image with Coq dependencies and enter shell with commands:

```
docker build -t nominal-ssprove .
docker run --rm -it -v ${PWD}:/mnt nominal-ssprove
```

It takes around an hour to build the image due to compilation of Coq dependencies, but progress should be evident by terminal output.
The final image is around 4GB in size and can be deleted with the command `docker rmi nominal-ssprove`.
