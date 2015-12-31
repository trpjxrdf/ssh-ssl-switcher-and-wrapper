
```
  WAIT FOR a first byte or SSL_FIRST_BYTE_WAIT_TIME (SSL_FIRST_BYTE_WAIT_TIME > 0)
  IF (SSL_FIRST_BYTE_WAIT_TIME > 0) AND time out THEN
     CONNECT TO IP4_SSH (without SSL)
  ELSE
      DO ssl hanshake (but no longer than SSL_HANDSHAKE_TIME)
      WAIT FOR a first byte or FIRST_BYTE_WAIT_TIME
      IF time out THEN
         CONNECT TO IP4_SSH (with SSL)
      ELSE
         WAIT FOR data of the SIGNATUREs bytes at least (but no longer than SIGNATURE_WAIT_TIME)
         IF SIGNATURE_RDP THEN
            CONNECT TO PORT_SIGNT_RDP
         ELSEIF SIGNATURE_1 THEN
            CONNECT TO IP4_SIGNT_1
         ELSE
            CONNECT TO IP4_HTTP
         ENDIF
      ENDIF
  ENDIF
```