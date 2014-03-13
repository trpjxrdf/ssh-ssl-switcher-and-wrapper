program SslSshSwitcherSsl;

{$mode objfpc}{$H+}
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
 MILLISECONDS_IN_DAY = 3600000 * 24;

 {$i SslSshSwitcherSsl.inc}

type
  PBuffer = ^TBuffer;
  TBuffer = array[0..4096 - 1] of byte;
  TPendingState = record
    state: (stNotUsed, stActive, stShutdown, stClosed);
    wantRead: boolean;
    wantWrite: boolean;
  end;

var
  conn: array[0..MAX_CONN - 1] of record
    status: (stFree, stWaitingSslFirstByte,
      stHandshake, stWaitingForFirstByte,
      stWaitingForSignature, stConnecting,
      stTunneling);
    timeoutTime: TDateTime;
    sock: array[0..1] of Tsocket;
    ssl: array[0..1] of PSSL;
    pending: array[0..1] of TPendingState;
    buf: array[0..1] of record
      size: SizeInt;
      data: PBuffer;
    end;
  end;
  freeConnCount: cint = 0;

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
const CRLF = #13#10;
      hostPattern = CRLF + 'Host: ';
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

  {$IFDEF LOG}
  procedure Log(level: TLogLevel; const msg: string);
  begin
    case level of
      logError: Write('ERROR: ');
      logWarn: Write('WARN: ');
      logInfo: Write('INFO: ');
    end;
    writeln(msg);
  end;
  {$ENDIF}

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

  function CheckSSLresult(ssl: PSSL; retcode: integer; const op: string; var pending: TPendingState; IgnoreSysCall: boolean = false): boolean;
  overload;
  var
    err: integer;
  begin
    Result := True;
    if retcode <> 1 then
    begin
      err := OpenSSL.SslGetError(ssl, retcode);
      Result := False;
      case err of
        SSL_ERROR_NONE: ;
        SSL_ERROR_SYSCALL: begin
            pending.wantRead:= true;
            if not IgnoreSysCall then begin
              if not(errno in [ESysEINPROGRESS, ESysEAGAIN]) then RaiseLastOSError;
            end;
        end;
        SSL_ERROR_WANT_READ: pending.wantRead:= true;
        SSL_ERROR_WANT_WRITE: pending.wantWrite:= true;
        SSL_ERROR_WANT_X509_LOOKUP,
        SSL_ERROR_WANT_CONNECT,
        SSL_ERROR_WANT_ACCEPT: begin
          pending.wantRead:= true;
          pending.wantWrite:= true;
        end
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
      for j := 0 to 1 do
      begin
        Dispose(conn[i].buf[j].Data);
        if conn[i].ssl[j] <> nil then begin
          SslFree(conn[i].ssl[j]);
          conn[i].ssl[j] := nil;
        end;
        if conn[i].sock[j] <> 0 then
        begin
          Sockets.CloseSocket(conn[i].sock[j]);
        end;
      end;
      FillChar(conn[i], sizeof(conn[i]), #0);
      Inc(freeConnCount);
      {$IFDEF LOG}Log(logInfo, 'freeConnCount=' + IntToStr(freeConnCount));{$ENDIF}
    end;
  end;

  {$IFDEF LOG}
  procedure LogException(eobj: TObject);
  begin
    if eobj is Exception then
    begin
      Log(logError, Exception(eobj).Message);
    end
    else
      Log(logError, 'Unknown error');
  end;
  {$ENDIF}

  procedure Recv0(i: cint; maxSize: cint);
  var
    n: integer;
    p: ^byte;
  begin
    with conn[i] do begin
      pending[0].wantRead := false;
      pending[0].wantWrite := false;
      while true do begin
        if pending[0].state <> stActive then exit;
        n := maxSize - buf[1].size;
        if n <= 0 then exit;
        p := @buf[1].Data^;
        Inc(p, buf[1].size);
        if ssl[0] <> nil then begin
          n := SslRead(ssl[0], p, n);
          if n > 0 then
            Inc(buf[1].size, n)
          else if n = 0 then
            pending[0].state := stClosed
          else begin
            CheckSSLresult(ssl[0], n, 'SslRead', pending[0]);
            break;
          end;
        end else begin
          n := Sockets.fprecv(sock[0], p, n, 0);
          if n > 0 then
            Inc(buf[1].size, n)
          else if n = 0 then
            pending[0].state := stClosed
          else begin
            if errno = ESysEAGAIN then begin
              pending[0].wantRead := true;
              break;
            end
            else
              RaiseLastOSError;
          end;
        end;
      end;
    end;
  end;

  procedure Tunnel(i: cint);

  var hasActivity: boolean;

  procedure DoSend(i, k: cint);
  var
    res: cint;
  begin
    with conn[i] do begin
      if ssl[k] <> nil then begin
        res := SslWrite(ssl[k], buf[k].Data, buf[k].size);
        if res > 0 then begin
          if res > buf[k].size then
            raise Exception.Create('res > buf[' + IntToStr(k) + '].size !');
          hasActivity := true;
          Dec(buf[k].size, res);
          if buf[k].size > 0 then begin
            Move(buf[k].Data^[res], buf[k].Data^, buf[k].size);
            pending[k].wantWrite := true;
          end;
        end else begin
          CheckSSLresult(ssl[k], res, 'SslWrite', pending[k]);
        end;
      end
      else
      begin
        res := Sockets.fpsend(sock[k], buf[k].Data, buf[k].size, 0);
        if res > 0 then begin
          if res > buf[k].size then
            raise Exception.Create('res > buf[' + IntToStr(k) + '].size !');
	  hasActivity := true;
          Dec(buf[k].size, res);
          if buf[k].size > 0 then begin
            Move(buf[k].Data^[res], buf[k].Data^, buf[k].size);
            pending[k].wantWrite := true;
          end;
        end else begin
          if errno = ESysEAGAIN then
            pending[k].wantWrite := true
          else
            RaiseLastOSError;
        end;
      end;
    end;
  end;

  function DoRecv(i, k: cint): boolean;
  const maxSize = sizeof(TBuffer);
  var
    n: integer;
    p: ^byte;
  begin
    with conn[i] do begin
      n := maxSize - buf[1-k].size;
      if n <= 0 then exit;
      p := @buf[1-k].Data^;
      Inc(p, buf[1-k].size);
      if ssl[k] <> nil then begin
        n := SslRead(ssl[k], p, n);
        if n > 0 then
          Inc(buf[1-k].size, n)
        else
        if n = 0 then
          pending[k].state := stClosed
        else begin
          CheckSSLresult(ssl[k], n, 'SslRead', pending[k]);
        end;
      end else begin
        n := Sockets.fprecv(sock[k], p, n, 0);
        if n > 0 then
          Inc(buf[1-k].size, n)
        else
        if n = 0 then
          pending[k].state := stClosed
        else begin
          if errno = ESysEAGAIN then
            pending[k].wantRead := true
          else
            RaiseLastOSError;
        end;
      end;
    end;
  end;

  var
    k, res: cint;
  begin
    hasActivity := false;
    with conn[i] do begin
      pending[0].wantRead := false;
      pending[0].wantWrite := false;
      pending[1].wantRead := false;
      pending[1].wantWrite := false;
      for k := 0 to 1 do begin
        repeat
          if buf[k].size > 0 then begin
            if pending[k].state <> stActive then
              buf[k].size := 0
            else begin
              DoSend(i, k);
            end;
          end;
          if buf[k].size > 0 then break;
          if pending[1-k].state = stActive then DoRecv(i, 1-k);
          if pending[1-k].state = stClosed then begin
            if pending[k].state in [stActive, stShutdown] then begin
              pending[k].state := stShutdown;
              if ssl[k] <> nil then begin
                res := SslShutdown(ssl[k]);
                if res > 0 then
                  pending[k].state := stClosed
                else begin
                  CheckSSLresult(ssl[k], res, 'SslShutdown', pending[k], true);
                  pending[k].wantRead := true;
                end;
              end else begin
                res := fpshutdown(sock[k], 2);
                if res <> 0 then RaiseLastOSError;
                pending[k].state := stClosed;
              end;
            end;
            if pending[k].state = stClosed then begin
              FreeConn(i, true);
              exit;
            end;
          end;
        until buf[k].size = 0;
      end;
      if hasActivity then begin
        SetTimeout(timeoutTime, IDDLE_TIMEOUT);
      end;
    end;
  end;

var
  ctx: PSSL_CTX;
  server, client: Tsocket;
  bindAddr: TSockAddr;
  clientAddr: TSockAddr;
  res: cint;
  len: tsocklen;
  fdr, fdw: TFDSet;
  i, j: integer;

  procedure FirstDataWaitCompleted(i: integer; connType: TConnectionType);
  var
    addr: TSockAddr;
    res: cint;
  begin
    with conn[i] do
    begin
      FillChar(addr, sizeof(addr), #0);
      addr.sin_family := AF_INET;
      addr.sin_addr := Targets[connType].addr;
      addr.sin_port := htons(Targets[connType].port);
      conn[i].sock[1] := Sockets.fpsocket(AF_INET, SOCK_STREAM, 0);
      SetSocketOptions(sock[1]);
      res := Sockets.fpconnect(sock[1], @addr, sizeof(addr));
      if (res = -1) and not (errno in [ESysEINPROGRESS, ESysEAGAIN]) then RaiseLastOSError;
      if Targets[connType].ssl then begin
        ssl[1] := SslNew(ctx);
        CheckSSLresult(ssl[1], SslSetFd(ssl[1], sock[1]), 'SslSetFd', pending[1]);
        CheckSSLresult(ssl[1], SslConnect(ssl[1]), 'SslConnect', pending[1]);
      end;
      with pending[1] do begin
        wantWrite := true;
        state := stActive;
      end;
      status := stConnecting;
      SetTimeout(timeoutTime, CONNECT_TIMEOUT);
    end;
  end;

var
  sa, sa2: sigactionrec;
  tmpps: TPendingState;
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
      CheckSSLresult(nil, 0, 'SslCtxNew', tmpps);
    try

      CheckSSLresult(nil,
        SslCtxUseCertificateChainFile(ctx, CERT_FILE_NAME),
        'SslCtxUseCertificateChainFile', tmpps
        );
      CheckSSLresult(nil,
        SslCtxUsePrivateKeyFile(ctx, KEY_FILE_NAME, SSL_FILETYPE_PEM),
        'SslCtxUsePrivateKeyFile', tmpps
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
          if freeConnCount > 0 then fpFD_SET(server, fdr);
          for i := 0 to high(conn) do
            with conn[i] do begin
              if status = stFree then continue;
              if (pending[0].state in [stNotUsed, stClosed])
              and(pending[1].state in [stNotUsed, stClosed]) then begin
                FreeConn(i, False);
              end else begin
                for j := 0 to 1 do begin
                  if pending[j].state in [stActive, stShutdown] then begin
                    if pending[j].wantRead  then fpFD_SET(sock[j], fdr);
                    if pending[j].wantWrite then fpFD_SET(sock[j], fdw);
                  end;
                end;
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
              if status = stFree then continue;
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
                    {$IFDEF LOG}Log(logWarn, 'Iddle timeout');{$ENDIF}
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
                  if fpFD_ISSET(sock[0], fdr) <> 0 then begin
                    pending[0].wantRead := true;
                    pending[0].wantWrite := false;
                    ssl[0] := SslNew(ctx);
                    CheckSSLresult(ssl[0], SslSetFd(ssl[0], sock[0]), 'SslSetFd', pending[0]);
                    status := stHandshake;
                    SetTimeout(timeoutTime, SSL_HANDSHAKE_TIME);
                  end;
                end;
                if status = stHandshake then
                begin
                  if TimeReached(timeoutTime) then
                  begin
                    {$IFDEF LOG}Log(logWarn, 'SSL handshake timeout');{$ENDIF}
                    FreeConn(i, False);
                  end
                  else
                  if fpFD_ISSET(sock[0], fdr) <> 0 then
                  begin
                    pending[0].wantRead := false;
                    pending[0].wantWrite := false;
                    if CheckSSLresult(ssl[0], SslAccept(ssl[0]), 'SslAccept', pending[0]) then begin
                      SetTimeout(conn[i].timeoutTime, FIRST_BYTE_WAIT_TIME);
                      pending[0].wantRead := true;
                      pending[0].wantWrite := false;
                      status := stWaitingForFirstByte;
                    end;
                  end;
                end;
                if status = stWaitingForFirstByte then
                begin
                  if TimeReached(timeoutTime) then begin
                    FirstDataWaitCompleted(i, ctSSH);
                  end else
                  if fpFD_ISSET(sock[0], fdr) <> 0 then begin
                    Recv0(i, sizeof(TBuffer) - length(HTTP_HOST_NAME));
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
                    {$IFDEF LOG}Log(logWarn, 'Wait signature timeout');{$ENDIF}
                    FreeConn(i, False);
                  end
                  else
                  if fpFD_ISSET(sock[0], fdr) <> 0 then
                  begin
                    Recv0(i, sizeof(TBuffer) - length(HTTP_HOST_NAME));
                    if (buf[1].size >= sizeof(SIGNATURE_RDP))
                    and(buf[1].size >= sizeof(SIGNATURE_1)) then begin
                      if CompareByte(buf[1].Data^, SIGNATURE_RDP[0], sizeof(SIGNATURE_RDP)) = 0 then begin
                        FirstDataWaitCompleted(i, ctRDP);
                      end else
                      if CompareByte(buf[1].Data^, SIGNATURE_1[0], sizeof(SIGNATURE_1)) = 0 then begin
                        Dec(buf[1].size, sizeof(SIGNATURE_1));
                        if buf[1].size > 0 then
                          Move(buf[1].Data^[sizeof(SIGNATURE_1)], buf[1].Data^, buf[1].size);
                        FirstDataWaitCompleted(i, ctCON1);
                      end else begin
                        if (buf[1].size >= sizeof(TBuffer) - length(HTTP_HOST_NAME))
                        or (FindBytePattern(buf[1].Data^, buf[1].size, CRLF + CRLF) >= 0) then begin
                          if length(HTTP_HOST_NAME) > 0 then ReplaceHost(buf[1].Data^, buf[1].size, sizeof(TBuffer), HTTP_HOST_NAME);
                          FirstDataWaitCompleted(i, ctHTTP);
                          pending[0].wantRead := true;
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
                    {$IFDEF LOG}Log(logWarn, 'Outgoing connection timeout');{$ENDIF}
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
                    {$IFDEF LOG}Log(logWarn, 'Outgoing connection error');{$ENDIF}
                    FreeConn(i, False);
                  end;
                end;
              except
                FreeConn(i, False);
                {$IFDEF LOG}LogException(ExceptObject);{$ENDIF}
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
                {$IFDEF LOG}Log(logInfo, 'freeConnCount=' + IntToStr(freeConnCount));{$ENDIF}
                with conn[i].pending[0] do begin
                  wantRead := true;
                  wantWrite := false;
                  state := stActive;
                end;
                SetTimeout(conn[i].timeoutTime, SSL_FIRST_BYTE_WAIT_TIME);
              end
              else
              begin
                {$IFDEF LOG}Log(logError, 'freeConnCount > 0 but no free conn found');{$ENDIF}
                Sockets.CloseSocket(client);
              end;
            except
              if client > 0 then
                Sockets.CloseSocket(client);
              if i >= 0 then
                FreeConn(i, False);
              {$IFDEF LOG}LogException(ExceptObject);{$ENDIF}
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
    {$IFDEF LOG}
    LogException(ExceptObject);
    {$ELSE}
    on E: Exception do writeln(E.Message);
    {$ENDIF}
  end;

end.

