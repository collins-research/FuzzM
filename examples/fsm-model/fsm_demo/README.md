# Building FSM Demo

To build only the fsm exe, perform the following steps:

1. `./run.sh`
2. In the docker container run `make`
3. *From another terminal* run `docker ps` and identify the container id of fsm
4. Run `docker commit <container id> fsm:latest`
5. The container started in step 1 can now be terminated
