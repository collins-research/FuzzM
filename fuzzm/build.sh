docker build --build-arg proxy_host=${PROXY_HOST} --build-arg proxy_port=${PROXY_PORT} -t fuzzmbuild:latest -f Dockerfile.Build .

docker create --name fuzzmmachine fuzzmbuild:latest
docker cp fuzzmmachine:/root/fuzzm/target/fuzzm-0.0.1-SNAPSHOT-jar-with-dependencies.jar ./fuzzm.jar
docker rm -f fuzzmmachine
echo "Boom. Done."
