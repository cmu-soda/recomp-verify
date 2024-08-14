#/bin/sh

java -jar ../../../../bin/recomp-verify.jar client_server_db_ae.tla client_server_db_ae.cfg C2.tla no_invs.cfg C1.inv \
C3.tla no_invs.cfg \
C4.tla no_invs.cfg \
C5.tla no_invs.cfg \
T5.tla no_invs.cfg
