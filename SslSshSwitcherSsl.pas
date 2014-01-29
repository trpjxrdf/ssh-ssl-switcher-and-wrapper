program SslSshSwitcherSsl;

{$mode objfpc}{$H+}

{DEFINE DEBUG}
{DEFINE LOG}

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

uses
  SysUtils,
  baseunix,
  sockets,
  openssl;

type
  TConnectionType = (ctSSH, ctHTTP, ctRDP, ctCON1);
  TLogLevel = (logError, logWarn, logInfo);

const
 {$i SslSshSwitcherSsl.inc}

  hostPattern = 'Host: ';

type
  PBuffer = ^TBuffer;
  TBuffer = array[0..4096 - 1] of byte;

var
  conn: array[0..MAX_CONN - 1] of record
    status: (stFree, stWaitingSslFirstByte,
      stHandshake, stWaitingForFirstByte,
      stWaitingForSignature, stConnecting,
      stTunneling);
    timeoutTime: TDateTime;
    sock: array[0..1] of Tsocket;
    ssl: PSSL; // ssl for sock[0]
    closed: array[0..1] of boolean;
    buf: array[0..1] of record
      size: SizeInt;
      data: PBuffer;
    end;
  end;

var
  server, client: Tsocket;
  bindAddr: TSockAddr;
  clientAddr: TSockAddr;
  res: cint;
  len: tsocklen;
  fdr, fdw: TFDSet;
  i, j: integer;
  freeConnCount: cint;

const CRLF = #13#10;

function FindBytePattern(const buf; size: SizeInt; const pattern: string): SizeInt;
var p: ^byte;
    i, L: SizeInt;
begin
  Result := 0;
  p := addr(buf);
  L := size - length(pattern) + 1;
  while Result < L do begin
    i := IndexByte(p^, size - Result, byte(pattern[1]));
    if i < 0 then begin
      Result := -1;
      exit;
    end;
    inc(p, i);
    inc(Result, i);
    if CompareByte(p^, pattern[1], length(pattern)) = 0 then exit;
    inc(p);
    inc(Result);
  end;
  Result := -1;
end;

function ReplaceHost(const buf; var size: SizeInt; maxSize: SizeInt; const newHost: string): boolean;
const CRLF: string = #13#10;
      hostPattern = 'Host: ';
var i, i2, newSize: integer;
    p1, p2, p3: ^byte;
begin
  Result := false;
  i := FindBytePattern(buf, size, hostPattern);
  if i < 0 then exit;
  i2 := FindBytePattern(buf, size, CRLF + CRLF);
  if i > i2 then exit;
  inc(i, length(hostPattern));
  p1 := addr(buf);
  inc(p1, i);
  i2 := FindBytePattern(p1^, size - i, CRLF);
  if i2 < 0 then exit;
  newSize := size - i2 + length(newHost);
  if newSize > maxSize then exit;
  p2 := p1;
  inc(p2, i2);
  p3 := p1;
  inc(p3, length(newHost));
  Move(p2^, p3^, size - i - i2);
  Move(newHost[1], p1^, length(newHost));
  size := newSize;
  Result := true;
end;

  // Routines to handle timeouts
var
  CurrentTime: TDateTime;
  waitTime: cint;

  function TimeReached(const timeVar: TDateTime): boolean;
  var
    d: double;
    w: cint;
  begin
    d := timeVar - CurrentTime;
    Result := d <= 0;
    if not Result then
    begin
      if d > 1 then
        d := 1;
      w := round(MILLISECONDS_IN_DAY * d);
      if (waitTime < 0) or (w < waitTime) then
        waitTime := w;
    end;
  end;

  procedure SetTimeout(var timeVar: TDateTime; delay: cint);
  begin
    timeVar := CurrentTime + delay / MILLISECONDS_IN_DAY;
    if (waitTime < 0) or (delay < waitTime) then
      waitTime := delay;
  end;

  //--------------------------------

  procedure RaiseSslError(err: integer; const op: string = '');
  var
    s: string;
  begin
    SetLength(s, 256);
    OpenSSL.ErrErrorString(err, s, length(s));
    if op = '' then
      raise Exception.Create('OpenSSL error: ' + s)
    else
      raise Exception.Create('OpenSSL error on "' + op + '": ' + s);
  end;

  function CheckSSLresult(ssl: PSSL; retcode: integer; const op: string): boolean;
  overload;
  var
    err: integer;
  begin
    Result := True;
    if retcode <> 1 then
    begin
      err := OpenSSL.SslGetError(ssl, retcode);
      case err of
        SSL_ERROR_NONE: ;
        SSL_ERROR_WANT_READ,
        SSL_ERROR_WANT_WRITE,
        SSL_ERROR_WANT_X509_LOOKUP,
        SSL_ERROR_WANT_CONNECT,
        SSL_ERROR_WANT_ACCEPT: Result := False;
        else
        begin
          RaiseSslError(err, op);
        end;
      end;
    end;
  end;

  procedure SetSocketOptions(s: Tsocket);
  var
    x: cint;
  begin
    x := FpFcntl(s, F_GETFL, 0);
    FpFcntl(s, F_SETFL, x or O_NONBLOCK);
  end;



  procedure ResetWaitTime;
  begin
    CurrentTime := Now;
    waitTime := -1;
  end;

  procedure FreeConn(i: integer; gracefully: boolean);
  var
    j: integer;
  begin
    if conn[i].status <> stFree then
    begin
      if conn[i].ssl <> nil then
      begin
        SslShutdown(conn[i].ssl);
        SslFree(conn[i].ssl);
      end;
      for j := 0 to 1 do
      begin
        if conn[i].sock[j] <> 0 then
        begin
          if gracefully then
            Sockets.fpshutdown(conn[i].sock[j], 2);
          Sockets.CloseSocket(conn[i].sock[j]);
        end;
        Dispose(conn[i].buf[j].Data);
      end;
      FillChar(conn[i], sizeof(conn[i]), #0);
      Inc(freeConnCount);
    end;
  end;

  procedure Log(level: TLogLevel; const msg: string);
  begin
  {$IFDEF LOG}
    case level of
      logError: Write('ERROR: ');
      logWarn: Write('WARN: ');
      logInfo: Write('INFO: ');
    end;
    writeln(msg);
  {$ENDIF}
  end;

  procedure LogException(eobj: TObject);
  begin
    if eobj is Exception then
    begin
      Log(logError, Exception(eobj).Message);
    end
    else
      Log(logError, 'Unknown error');
  end;

  function Recv0(i: cint; maxSize: cint): boolean;
  var
    n: integer;
    p: ^byte;
  begin
    with conn[i] do
    begin
      if closed[0] then
        exit;
      n := maxSize - buf[1].size;
      if n <= 0 then
        exit;
      p := @buf[1].Data[0];
      Inc(p, buf[1].size);
      if ssl <> nil then
      begin
        n := SslRead(ssl, p, n);
        if n > 0 then
        begin
          Inc(buf[1].size, n);
        end
        else
        if n = 0 then
        begin
          closed[0] := True;
        end
        else
        begin
          CheckSSLresult(ssl, n, 'SslRead');
        end;
      end
      else
      begin
        n := Sockets.fprecv(sock[0], p, n, 0);
        if n > 0 then
        begin
          Inc(buf[1].size, n);
        end
        else
        if n = 0 then
        begin
          closed[0] := True;
        end
        else
        if n < 0 then
        begin
          if errno <> ESysEAGAIN then
            RaiseLastOSError;
        end;
      end;
      Result := buf[1].size = maxSize;
    end;
  end;

  procedure Recv1(i: cint);
  var
    n: integer;
    p: ^byte;
  begin
    with conn[i] do
    begin
      if closed[1] then
        exit;
      n := sizeof(TBuffer) - buf[0].size;
      if n = 0 then
        exit;
      p := @buf[0].Data[0];
      Inc(p, buf[0].size);
      n := Sockets.fprecv(sock[1], p, n, 0);
      if n > 0 then
      begin
        Inc(buf[0].size, n);
      end
      else
      if n = 0 then
      begin
        closed[1] := True;
      end
      else
      if n < 0 then
      begin
        if errno <> ESysEAGAIN then
          RaiseLastOSError;
      end;
    end;
  end;

  function Send0(i: cint): boolean;
  var
    res: cint;
  begin
    with conn[i] do
    begin
      Result := False;
      if closed[0] then
        buf[0].size := 0;
      if buf[0].size = 0 then
        exit;
      if ssl <> nil then
      begin
        res := SslWrite(ssl, @buf[0].Data[0], buf[0].size);
        if res > 0 then
        begin
          if res > buf[0].size then
            raise Exception.Create('res > buf[0].size !');
          Dec(buf[0].size, res);
          if buf[0].size > 0 then
            Move(buf[0].Data[res], buf[0].Data[0], buf[0].size);
          Result := True;
        end
        else
        begin
          CheckSSLresult(ssl, res, 'SslWrite');
        end;
      end
      else
      begin
        res := Sockets.fpsend(sock[0], @buf[0].Data[0], buf[0].size, 0);
        if res > 0 then
        begin
          if res > buf[0].size then
            raise Exception.Create('res > buf[0].size !');
          Dec(buf[0].size, res);
          if buf[0].size > 0 then
            Move(buf[0].Data[res], buf[0].Data[0], buf[0].size);
          Result := True;
        end
        else
        begin
          if errno <> ESysEAGAIN then
            RaiseLastOSError;
        end;
      end;
    end;
  end;

  function Send1(i: cint): boolean;
  var
    res: cint;
  begin
    with conn[i] do
    begin
      Result := False;
      if closed[1] then
        buf[1].size := 0;
      if buf[1].size = 0 then
        exit;
      res := Sockets.fpsend(sock[1], @buf[1].Data[0], buf[1].size, 0);
      if res > 0 then
      begin
        if res > buf[1].size then
          raise Exception.Create('res > buf[j].size !');
        Dec(buf[1].size, res);
        if buf[1].size > 0 then
          Move(buf[1].Data[res], buf[1].Data[0], buf[1].size);
        Result := True;
      end
      else
      begin
        if errno <> ESysEAGAIN then
          RaiseLastOSError;
      end;
    end;
  end;

  procedure Tunnel(i: cint);
  var
    j, res: cint;
    hasActivity: boolean;
  begin
    with conn[i] do
    begin
      hasActivity := False;
      Recv0(i, sizeof(TBuffer));
      if status = stFree then
        exit;
      if Send1(i) then
        hasActivity := True;
      if status = stFree then
        exit;
      Recv1(i);
      if status = stFree then
        exit;
      if Send0(i) then
        hasActivity := True;
      if status = stFree then
        exit;
      if hasActivity then
      begin
        SetTimeout(timeoutTime, IDDLE_TIMEOUT);
      end;
    end;
  end;

  procedure FirstDataWaitCompleted(i: integer; connType: TConnectionType);
  var
    s: TSocket;
    addr: TSockAddr;
    res: cint;
  begin
    with conn[i] do
    begin
      FillChar(addr, sizeof(addr), #0);
      addr.sin_family := AF_INET;
      addr.sin_addr := Targets[connType].addr;
      addr.sin_port := htons(Targets[connType].port);
      s := Sockets.fpsocket(AF_INET, SOCK_STREAM, 0);
      try
        SetSocketOptions(s);
        res := Sockets.fpconnect(s, @addr, sizeof(addr));
        if (res = -1) and (errno <> ESysEINPROGRESS) then
          RaiseLastOSError;
        sock[1] := s;
        s := 0;
        status := stConnecting;
        SetTimeout(timeoutTime, CONNECT_TIMEOUT);
      finally
        if s <> 0 then
          Sockets.CloseSocket(s);
      end;
    end;
  end;

var
  ctx: PSSL_CTX;
  b: boolean;
  sa, sa2: sigactionrec;
begin
  PtrInt(sa.sa_handler) := SIG_IGN;
  sa.sa_mask[0] := 0;
  sa.sa_flags := 0;
  fpsigaction(SIGPIPE, @sa, @sa2);
  try

    SslLoadErrorStrings;
    OpenSSL_add_all_algorithms;
    // OpenSSL_add_all_ciphers;
    // OpenSSL_add_all_digests;

    ctx := OpenSSL.SslCtxNew(OpenSSL.SslMethodV23);
    if ctx = nil then
      CheckSSLresult(nil, 0, 'SslCtxNew');
    try

      CheckSSLresult(nil,
        SslCtxUseCertificateChainFile(ctx, CERT_FILE_NAME),
        'SslCtxUseCertificateChainFile'
        );
      CheckSSLresult(nil,
        SslCtxUsePrivateKeyFile(ctx, KEY_FILE_NAME, SSL_FILETYPE_PEM),
        'SslCtxUsePrivateKeyFile'
        );

      ResetWaitTime;
      fillchar(conn, sizeof(conn), #0);
      freeConnCount := length(conn);

      server := Sockets.fpsocket(AF_INET, SOCK_STREAM, 0);
      if server < 0 then
        RaiseLastOSError;
      try

        bindAddr.sin_family := AF_INET;
        bindAddr.sin_addr.s_addr := INADDR_ANY;
        bindAddr.sin_port := htons(PORT_LISTEN);

        res := Sockets.fpbind(server, @bindAddr, sizeof(bindAddr));
        if res < 0 then
          RaiseLastOSError;

        res := Sockets.fplisten(server, 5);
        if res < 0 then
          RaiseLastOSError;

        repeat

          // prepare signal`s arrays to wait
          fpFD_ZERO(fdr);
          fpFD_ZERO(fdw);
          if freeConnCount > 0 then
            fpFD_SET(server, fdr);
          for i := 0 to high(conn) do
            with conn[i] do
            begin
              case status of
                stHandshake,
                stWaitingSslFirstByte,
                stWaitingForFirstByte,
                stWaitingForSignature:
                begin
                  if closed[0] then
                    FreeConn(i, False)
                  else
                    fpFD_SET(sock[0], fdr);
                end;
                stConnecting:
                begin
                  {TODO check client connection status}
                  if closed[0] then
                    FreeConn(i, False)
                  else
                  begin
                    fpFD_SET(sock[1], fdr);
                    fpFD_SET(sock[1], fdw);
                  end;
                end;
                stTunneling:
                begin
                  if (closed[0] and closed[1]) and
                    ((closed[0] and (buf[1].size = 0)) or
                    (closed[1] and (buf[0].size = 0))) then
                  begin
                    FreeConn(i, False);
                  end
                  else
                  begin
                    for j := 0 to 1 do
                    begin
                      if buf[1 - j].size < sizeof(TBuffer) then
                      begin
                        if not closed[j] then
                        begin
                          fpFD_SET(sock[j], fdr);
                        end;
                      end
                      else
                      begin
                        if not closed[1 - j] then
                        begin
                          fpFD_SET(sock[1 - j], fdw);
                        end;
                      end;
                    end;
                  end;
                end;
                stFree: ;
              end;
            end;

          // wait for signals
          repeat
            res := fpselect(FD_MAXFDSET, @fdr, @fdw, nil, waitTime);
          until (res >= 0) or (errno <> ESysEINTR);
          if res < 0 then
            RaiseLastOSError;

          ResetWaitTime;

          // process signals
          for i := 0 to high(conn) do
            with conn[i] do
            begin
              if status = stFree then
                continue;
              try
                if status = stTunneling then
                begin
                  if (fpFD_ISSET(sock[0], fdr) <> 0) or
                    (fpFD_ISSET(sock[0], fdw) <> 0) or
                    (fpFD_ISSET(sock[1], fdr) <> 0) or
                    (fpFD_ISSET(sock[1], fdw) <> 0) then
                    Tunnel(i);
                  if (status = stTunneling) and
                    TimeReached(timeoutTime) then
                  begin
                    FreeConn(i, False);
                    Log(logWarn, 'Iddle timeout');
                  end;
                  continue;
                end;
                if status = stWaitingSslFirstByte then
                begin
                  if (SSL_FIRST_BYTE_WAIT_TIME > 0) and
                    TimeReached(timeoutTime) then
                  begin
                    FirstDataWaitCompleted(i, ctSSH);
                  end
                  else
                  if fpFD_ISSET(sock[0], fdr) <> 0 then
                  begin
                    conn[i].ssl := SslNew(ctx);
                    CheckSSLresult(conn[i].ssl, SslSetFd(conn[i].ssl, conn[i].sock[0]),
                      'SslSetFd');
                    conn[i].status := stHandshake;
                    SetTimeout(conn[i].timeoutTime, SSL_HANDSHAKE_TIME);
                  end;
                end;
                if status = stHandshake then
                begin
                  if TimeReached(timeoutTime) then
                  begin
                    Log(logWarn, 'SSL handshake timeout');
                    FreeConn(i, False);
                  end
                  else
                  if fpFD_ISSET(sock[0], fdr) <> 0 then
                  begin
                    if CheckSSLresult(ssl, SslAccept(ssl), 'SslAccept') then
                    begin
                      SetTimeout(conn[i].timeoutTime, FIRST_BYTE_WAIT_TIME);
                      status := stWaitingForFirstByte;
                    end;
                  end;
                end;
                if status = stWaitingForFirstByte then
                begin
                  if TimeReached(timeoutTime) then
                  begin
                    FirstDataWaitCompleted(i, ctSSH);
                  end
                  else
                  if fpFD_ISSET(sock[0], fdr) <> 0 then
                  begin
                    Recv0(i, sizeof(TBuffer) - length(hostPattern));
                    if conn[i].buf[1].size > 0 then
                    begin
                      SetTimeout(conn[i].timeoutTime, SIGNATURE_WAIT_TIME);
                      status := stWaitingForSignature;
                    end;
                  end;
                end;
                if status = stWaitingForSignature then
                begin
                  if TimeReached(timeoutTime) then
                  begin
                    Log(logWarn, 'Wait signature timeout');
                    FreeConn(i, False);
                  end
                  else
                  if fpFD_ISSET(sock[0], fdr) <> 0 then
                  begin
                    b := Recv0(i, sizeof(TBuffer) - length(hostPattern));
                    if (buf[1].size >= sizeof(SIGNATURE_RDP))
                    and(buf[1].size >= sizeof(SIGNATURE_1)) then begin
                      if CompareByte(buf[1].Data[0], SIGNATURE_RDP[0], sizeof(SIGNATURE_RDP)) = 0 then begin
                        FirstDataWaitCompleted(i, ctRDP);
                      end else
                      if CompareByte(buf[1].Data[0], SIGNATURE_1[0], sizeof(SIGNATURE_1)) = 0 then begin
                        Dec(buf[1].size, sizeof(SIGNATURE_1));
                        if buf[1].size > 0 then
                          Move(buf[1].Data[sizeof(SIGNATURE_1)], buf[1].Data[0], buf[1].size);
                        FirstDataWaitCompleted(i, ctCON1);
                      end else begin
                        if b or (FindBytePattern(buf[1].Data[0], buf[1].size, CRLF + CRLF) >= 0) then begin
                          if length(HTTP_HOST_NAME) > 0 then ReplaceHost(buf[1].Data[0], buf[1].size, sizeof(TBuffer), HTTP_HOST_NAME);
                          FirstDataWaitCompleted(i, ctHTTP);
                        end;
                      end;
                    end;
                  end;
                end;
                if status = stConnecting then
                begin
                  {TODO check client connection status}
                  if TimeReached(timeoutTime) then
                  begin
                    Log(logWarn, 'Outgoing connection timeout');
                    FreeConn(i, False);
                  end
                  else
                  if fpFD_ISSET(sock[1], fdw) <> 0 then
                  begin
                    SetTimeout(timeoutTime, IDDLE_TIMEOUT);
                    status := stTunneling;
                    Tunnel(i);
                  end
                  else
                  if fpFD_ISSET(sock[1], fdr) <> 0 then
                  begin
                    Log(logWarn, 'Outgoing connection error');
                    FreeConn(i, False);
                  end;
                end;
              except
                FreeConn(i, False);
                LogException(ExceptObject);
              end;
            end;
          // process accept
          if (freeConnCount > 0) and (fpFD_ISSET(server, fdr) <> 0) then
          begin
            client := 0;
            i := -1;
            try
              len := sizeof(clientAddr);
              client := fpaccept(server, @clientAddr, @len);
              if client <= 0 then
                RaiseLastOSError;
              SetSocketOptions(client);
              // search for free conn
              i := high(conn);
              while (i >= 0) and (conn[i].status <> stFree) do
                Dec(i);
              if i >= 0 then
              begin
                // add new conn
                fillchar(conn[i], sizeof(conn[i]), #0);
                conn[i].sock[0] := client;
                client := 0;
                conn[i].status := stWaitingSslFirstByte;
                New(conn[i].buf[0].Data);
                New(conn[i].buf[1].Data);
                Dec(freeConnCount);
                SetTimeout(conn[i].timeoutTime, SSL_FIRST_BYTE_WAIT_TIME);
              end
              else
              begin
                Log(logError, 'freeConnCount > 0 but no free conn found');
                Sockets.CloseSocket(client);
              end;
            except
              if client > 0 then
                Sockets.CloseSocket(client);
              if i >= 0 then
                FreeConn(i, False);
              LogException(ExceptObject);
            end;
          end;
        until False;


      finally
        Sockets.CloseSocket(server);
      end;

    finally
      if ctx <> nil then
        OpenSSL.SslCtxFree(ctx);
    end;

  except
    LogException(ExceptObject);
  end;

end.

