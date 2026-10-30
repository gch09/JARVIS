@echo off
chcp 65001 >nul
cd /d "%~dp0"

where python >nul 2>nul
if %errorlevel% neq 0 (
    echo Python이 설치되어 있지 않습니다.
    echo https://www.python.org/downloads/ 에서 Python을 설치한 뒤 다시 실행해주세요.
    echo 설치 시 "Add python.exe to PATH" 체크박스를 꼭 켜주세요.
    pause
    exit /b
)

rem 자비스 서버가 오류로 꺼지면 3초 뒤 자동으로 다시 켭니다 (화면도 자동으로 다시 연결됨).
rem 꺼진 이유는 jarvis_crash.txt 에 남습니다. Ctrl+C 로 끄면 다시 켜지지 않습니다.
set RESTARTS=0
:run
python jarvis_server.py
if %errorlevel% equ 0 goto done
set /a RESTARTS+=1
echo.
echo [JARVIS] 서버가 오류로 꺼졌어요. 이유는 jarvis_crash.txt 에 적어 뒀어요.
if %RESTARTS% geq 10 (
    echo [JARVIS] 10번 넘게 꺼져서 자동 재시작을 멈춥니다. jarvis_crash.txt 를 확인해 주세요.
    goto done
)
echo [JARVIS] 3초 뒤 다시 켭니다... (%RESTARTS%번째)
ping -n 4 127.0.0.1 >nul
goto run

:done
pause
