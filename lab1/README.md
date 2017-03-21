# Principles and Practice in Programming Languages Labs

This repository contains the student project files.

Refer to the lab handouts for details about each assignment.  This file provides some information to help you get started with setting up your development environment.

## Repository Organization

In the directory that you want your project files, clone this repository to your local machine using the following command:

    $ git clone https://github.com/bechang/pppl-labs.git
    
In this document, the

    $ 

simply stands for the shell prompt.

The above command will create the directory ``pppl-labs.`` Change into that directory

    $ cd pppl-labs
    
All other commands in this document will assume that your are in this directory.

The files for a single lab are committed on a different branch. For example, to switch to the Lab 1 branch, use the following command:

    $ git checkout --track origin/lab1
    
## Project Files Organization

For Lab 1, the most important project files are shown below.

```
.
├── README.md  (this file)
├── jsy.sh     (run through a .jsy through Node.js)
├── lab1.sh    (run your Javascripty intepreter)
├── src
│   ├── main
│   │   └── scala
│   │       └── jsy
│   │           ├── lab1                 (lab-specific support files will here)
│   │           │   ├── Parser.scala
│   │           │   └── ast.scala           (the Javascripty AST classes)
│   │           ├── student              (files for you to edit will be here)
│   │           │   ├── Lab1.scala          (implementation template to **submit**)
│   │           │   └── Lab1Worksheet.sc    (a scratch worksheet)
│   │           └── util
│   └── test
│       ├── resources
│       │   └── lab1    (test .jsy files with expect answers in .ans)
│       │       ├── test101_arith.ans
│       │       ├── test101_arith.jsy
│       │       ├── test102_divbyzero.ans
│       │       └── test102_divbyzero.jsy
│       └── scala
│           └── Lab1Spec.scala   (your ScalaTest unit tests)
└── testlab1.sh  (run your Lab1Spec)
```

The files for you to edit and submit will be in ``src/main/jsy/student``.

## Scala Development Tools

We will support [IntelliJ IDEA](https://www.jetbrains.com/idea/) on the [CU CS Virtual Machine](https://foundation.cs.colorado.edu/vm/) for development in this course. You are welcome to use any development environment, but we may not be able answer questions in your particular environment.

After setting up the CU CS VM, you will need to [download](https://www.jetbrains.com/idea/download/) and install IntelliJ IDEA. The Community Edition will be fine.

The project is designed to work with [Scala](http://www.scala-lang.org/) is 2.10. We will standardize on 2.10.5 (the latest Scala 2.10). The project files have not yet been ported to Scala 2.11. For the most part, you do not need to worry about the Scala version because we are using ``sbt`` for building.

### IntelliJ Import

From the IntelliJ splash screen on start up, first configure your Java software development kit (Java SDK) in IntelliJ

    Configure > Project Defaults > Project Structure

Under Project SDK, select an SDK from the list (either 1.7 or 1.8 are fine). If there are no listed, you will have to select the directory with your SDK from

    New ...

On the CU CS Virtual Machine, follow this procedure:

    New ... > JDK
    
And the select the following directory:

    /usr/lib/jvm/default-java

Then, again from the splash 

    Import Project

and then select the directory with the project files (i.e., ``pppl-labs``) and hit Ok. On the next dialog, select

    Import project from external model > SBT > Next

If you do not see SBT, then you did not select the project files. 

On the next dialog, select

    Use auto-import
      
If you want to be able to navigate to definitions in external sources, you can select to download sources and docs before hitting Finish.

Here is the IntelliJ documentation on [import](https://www.jetbrains.com/idea/help/getting-started-with-sbt.html#import_project).

### Command-Line Tools

While strictly required, you will also want to be use the command-line tools.

You can issue the following command to compile your code:

    $ sbt compile
    
This command

    $ sbt clean

deletes the previous compilation.

It is often convenient to run sbt interactively

    $ sbt
    
and then run via

    > compile

at the sbt prompt. The slow load time of sbt is due to starting a JVM instance, which is saved by starting it once and re-using the instance for several operations.

### Scala Interactive Console

From the command-line, you can start the Scala console using the command

    $ sbt console

and can import the functions in your lab in the following way

    scala> import jsy.student.Lab1._

In IntelliJ, you can start a Scala console with the project files available by selecting

    Tools > Run Scala Console
    
However, for quick experimentation in IntelliJ, it is more convenient to use a Scala Worksheet (e.g., ``src/scala/jsy/student/Lab1Worksheet.sc``).

## ScalaTest

We will be using the [ScalaTest](http://www.scalatest.org/) framework for unit testing.  Using this framework, we practice test-driven development (TDD), a standard practice in industry. You do not need to explicitly download ScalaTest.

We provide some unit tests in ``src/test/scala/Lab1Spec.scala`` to drive your implementation.  To run tests, right-click on the Lab1Spec object in the Project view and select

    Run 'Lab1Spec'
    
You can also run all test objects under the ``src/test`` directory via

    $ sbt test
    
Or you can specify, specifically

    $ sbt test-only Lab1Spec
    
For your convenience, we have a script

    $ ./testlab1.sh
    
to run Lab1Spec using sbt.

## Your Javascripty Interpreter

You can run your Javascripty interpreter with a file (e.g., tests in ``src/test/resources``) in IntelliJ by setting up a Run/Debug Configuration.

    Run > Edit Configurations ...

It may be easier to run your Javascripty interpreter on the command-line.

    $ sbt runMain jsy.student.Lab1 <arguments>

Or for your convenience,

    $ ./lab1.sh <arguments>
    
For quick experimentation, it is more convenient to use the Scala Console window (in IntelliJ or on the command-line) or a Scala Worksheet (in IntelliJ).

## Node.js

We have a script to run Javascripty files through Node.js (as JavaScript):

    $ ./jsy.sh test.jsy
