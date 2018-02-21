FROM maven:3.3.9

WORKDIR /root/jfuzz

CMD [ "-Dhttp.proxyHost=secproxy.rockwellcollins.com", \
      "-Dhttp.proxyPort=9090", \
      "-Dhttps.proxyHost=secproxy.rockwellcollins.com", \
      "-Dhttps.proxyPort=9090", \
      "-f", \
      "src/java/jfuzz", \
      "clean", \
      "compile", \
      "assembly:single"]

ENTRYPOINT [ "mvn"]
