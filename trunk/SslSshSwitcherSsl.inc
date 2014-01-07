      PORT_LISTEN = 5000;

      HTTP_HOST_NAME = 'news2.ru'; // to replace "Host: " in HTTP header. Or empty.

      Targets: array[TConnectionType] of record addr: in_addr; port: word; end = (
         (addr: (s_bytes: (127, 0, 0, 1)); port: 22), // SSH
         (addr: (s_bytes: (95, 170, 128, 218)); port: 80), // HTTP
         (addr: (s_bytes: (127, 0, 0, 1)); port: 3000), // CON1
         (addr: (s_bytes: (192, 168, 7, 134)); port: 3389) // RDP
      );

      CERT_FILE_NAME = 'SSL_Server.crt';
      KEY_FILE_NAME = 'Key1.pem';

      SIGNATURE_1: packed array[0..3] of byte = (0, 34, 212, 7);
      SIGNATURE_RDP: packed array[0..2] of byte = (3, 0, 0);

      SSL_FIRST_BYTE_WAIT_TIME = 0; // ms, 0 - disabled
      FIRST_BYTE_WAIT_TIME = 1000; // ms
      SIGNATURE_WAIT_TIME = 5000; // ms
      SSL_HANDSHAKE_TIME = 5000; // ms
      CONNECT_TIMEOUT = 5000; // ms
      IDDLE_TIMEOUT = 1000 * 60 * 10; // ms

      BUFFER_SIZE = 4096; // bytes

      MAX_CONN = (FD_MAXFDSET - 1) div 2;
      MILLISECONDS_IN_DAY = 3600000 * 24;

{
  -- ALGORITHM --
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

  Any CONNECT not longer than CONNECT_TIMEOUT
  IDDLE_TIMEOUT for any connection

}