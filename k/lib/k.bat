@ECHO off
SETLOCAL ENABLEEXTENSIONS
IF ERRORLEVEL 1 ECHO Unable to enable extensions
call "%~dp0\setenv.bat"
IF NOT DEFINED K_OPTS SET K_OPTS=-Xms64m -Xmx1024m -Xss32m -XX:+TieredCompilation
IF DEFINED K_NAILGUN ng.exe org.kframework.main.Main %*
IF NOT DEFINED K_NAILGUN java  -Djava.awt.headless=true -ea %K_OPTS% -cp "%~dp0..\lib\java\*" org.kframework.main.Main %*
ENDLOCAL
