
You can run the deployed Docker image like this:
```shell
docker run --rm -i ghcr.io/protocolconvergence/protocon:latest -x - -o - < examplespec/ColorRing.prot
```

A GitHub workflow builds and pushes that `ghcr.io/protocolconvergence/protocon:latest` image whenever we merge to the `deploy` or `release` branch.
That workflow doesn't use `compose.yml`, but it makes manual testing easier.

The process is basically:
```shell
bazel build -c opt //...
docker compose build
docker run --rm -i protocon -x - -o - < ../../examplespec/ColorRing.prot
```
