# Docker Setup

## Install Docker

[Docker CE](https://www.docker.com/community-edition#/download)

## Install Docker Compose

[Docker Compose](https://docs.docker.com/compose/install/#install-compose)

## Login to Server

To use any images from the server or push new images, one must login first

`docker login eisgit.rockwellcollins.com:4567`

### Run JFuzz

`docker-compose up`

### Docker Build

`docker build -t eisgit.rockwellcollins.com:4567/cyber/mbf/ts/mbfuzz/jfuzz:latest .`

### Docker Push

`docker push eisgit.rockwellcollins.com:4567/cyber/mbf/ts/mbfuzz/jfuzz:latest`