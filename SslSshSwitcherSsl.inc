      PORT_LISTEN = 5000;

      PORT_HTTP = 80;
      IP4_HTTP: in_addr = (s_bytes: (198, 41, 187, 201));

      PORT_SSH = 22;
      IP4_SSH: in_addr = (s_bytes: (127, 0, 0, 1));

      PORT_SIGNT_1 = 3000;
      IP4_SIGNT_1: in_addr = (s_bytes: (127, 0, 0, 1));

      PORT_SIGNT_RDP = 3389;
      IP4_SIGNT_RDP: in_addr = (s_bytes: (192, 168, 7, 134));

      CERT_FILE_NAME = 'SSL_Server.crt';
      KEY_FILE_NAME = 'Key1.pem';

      SIGNATURE_1: packed array[0..3] of byte = (0, 34, 212, 7);
      SIGNATURE_RDP: packed array[0..2] of byte = (3, 0, 0);

      SSL_FIRST_BYTE_WAIT_TIME = 000; // ms, 0 - disabled
      FIRST_BYTE_WAIT_TIME = 1000; // ms
      SIGNATURE_WAIT_TIME = 5000; // ms
      SSL_HANDSHAKE_TIME = 5000; // ms
      CONNECT_TIMEOUT = 5000; // ms
      IDDLE_TIMEOUT = 1000 * 60 * 10; // ms

      BUFFER_SIZE = 4096; // bytes

      MAX_CONN = (FD_MAXFDSET - 1) div 2;
      MILLISECONDS_IN_DAY = 3600000 * 24;


