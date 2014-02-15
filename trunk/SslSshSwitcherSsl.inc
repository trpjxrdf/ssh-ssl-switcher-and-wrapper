      PORT_LISTEN = 3000;

      //HTTP_HOST_NAME = 'www.forexpf.ru'; // to replace "Host: " in HTTP header. Or empty.
      HTTP_HOST_NAME = 'connect.raiffeisen.ru';

      Targets: array[TConnectionType] of record ssl: boolean; addr: in_addr; port: word; end = (
         (ssl: false; addr: (s_bytes: (127, 0, 0, 1)); port: 22), // SSH
         (ssl: true;  addr: (s_bytes: (193, 28, 44, 148)); port: 443), // HTTP
         (ssl: false; addr: (s_bytes: (127, 0, 0, 1)); port: 3000), // CON1
         (ssl: false; addr: (s_bytes: (192, 168, 7, 134)); port: 3389) // RDP
      );

      CERT_FILE_NAME = 'SSL_Server.crt';
      KEY_FILE_NAME = 'Key1.pem';

      SIGNATURE_1: packed array[0..3] of byte = (0, 34, 212, 7);
      SIGNATURE_RDP: packed array[0..2] of byte = (3, 0, 0);

      SSL_FIRST_BYTE_WAIT_TIME = 1000; // ms, 0 - disabled
      FIRST_BYTE_WAIT_TIME = 1000; // ms
      SIGNATURE_WAIT_TIME = 5000; // ms
      SSL_HANDSHAKE_TIME = 5000; // ms
      CONNECT_TIMEOUT = 5000; // ms
      IDDLE_TIMEOUT = 60 * 1000 * 10; // ms

      BUFFER_SIZE = 4096; // bytes

      MAX_CONN = (FD_MAXFDSET - 1) div 2;


