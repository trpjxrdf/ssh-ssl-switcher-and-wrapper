Features:

  1. detects SSH, HTTPS, SSH over HTTPS, RDP over HTTPS. SSH is detected by timeout in first data receiving immediatelly after connection (SSH protocol requires server to send data first but HTTP, RDP otherwise).
  1. written in Free Pascal
  1. developed for Linux systems. Tested under Ubuntu and Debian.
  1. configuration settings is in the include file SslSshSwitcherSsl.inc and requires compilation after changed
  1. uses non-blocking sockets and only one thread using "select" to wait events (low memory and CPU consumption)
  1. max. connection handled = (MAX\_CONN - 1 ) / 2. MAX\_CONN depends on system, usually 1024 for ubuntu and debian.

Read wiki pages how to install and use