# Beginning (Will be set up on Intellij)

### Download Intellij
Have all import settings enabled

### Setting up intellij
- Change the output folder to be recomp-verify/bin
- For artifacts add recom-verify.jar
- Mark ``tlatools/org.lamport.tlatools/src`` as source path for "Main Class" for recomp-verify.jar


### Adding libraries
go to /bin and right click LTS-Robustness.jar and [whatever] and select ``Add as library..`` and add as project library

Then in tlatools/ go to org.lamport.tools/bin and right click all those bad boys and add all of them as libraries.

### In build artficats
Set up the main class as: tlc2/Main

### Current status:
Issues compiling in RecompVerify.java 
