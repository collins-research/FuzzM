# FuzzM

This is the source code repository for FuzzM.

## Fuzzm Development

FuzzM has been developed in Eclipse under JDK 8.  It should be
possible to import this project into Eclipse as an existing
repository by navigating in Eclipse to the `FuzzM/fuzzm/fuzzm` directory.
You will need to have Maven installed to build FuzzM in Eclipse.

## Updating JKind in the Mavin Local Repository

FuzzM leverages class files from JKind.  It is possible to
update the version of JKind with which FuzzM is built.  To do so,
execute the folowing command:

`./scripts/jkind-mvn-install.sh /path/to/jkind.jar`

Note that version of JKind installed here is being used in the
development of FuzzM.  As such, any imported JKind libraries must be
fully extracted into the .jar file.  In Eclipse, this can be
accomplished by selecting the 'extract required libraries into
generated JAR' radio button during the Export... -> Java -> Runnable
JAR file process.  The .jar file distributed with JKind **will not work**
for this purpose.

Note also that this version of JKind is *not* necessarily used as a
solver.  The version of JKind used as a solver when running FuzzM will
be determined by either your $PATH or your Docker config file.
