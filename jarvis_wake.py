import json
import os
import subprocess
import sys
import time
import urllib.request
import webbrowser

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
PORT = 5005
URL = f"http://localhost:{PORT}/"
DEBUG = "--debug" in sys.argv

WAKE_MODEL_NAME = "hey_jarvis"
WAKE_THRESHOLD = 0.3
CLAP_MIN_PEAK = 0.15
CLAP_OVER_NOISE = 6.0
MIC_GAIN = 12.0
CLAP_MIN_GAP = 0.12
CLAP_MAX_GAP = 0.9
COOLDOWN_SEC = 6

SAMPLE_RATE = 16000
BLOCK = 320
OWW_CHUNK = 1280


def log(msg):
    if sys.stdout is None:
        return
    print(f"[깨우기] {msg}", flush=True)


def server_state():
    try:
        with urllib.request.urlopen(URL + "alive", timeout=1.5) as r:
            return bool(json.loads(r.read().decode("utf-8")).get("tab"))
    except Exception:
        return None


def wake_jarvis(reason):
    state = server_state()
    if state is True:
        return
    if state is None:
        py = sys.executable
        if py.lower().endswith("pythonw.exe"):
            py = py[:-5] + ".exe"
        flags = getattr(subprocess, "CREATE_NEW_CONSOLE", 0)
        subprocess.Popen([py, os.path.join(BASE_DIR, "jarvis_server.py")],
                         cwd=BASE_DIR, creationflags=flags)
    else:
        webbrowser.open(URL)


class ClapDetector:
    def __init__(self):
        self.noise = 0.02
        self.prev_peak = 0.0
        self.first_at = 0.0
        self.last_at = 0.0
        self.loud_blocks = 0

    def feed(self, peak, rms, now):
        hit = False
        threshold = max(CLAP_MIN_PEAK, self.noise * CLAP_OVER_NOISE)
        sharp = peak > threshold and self.prev_peak < peak * 0.5 and peak > rms * 3.5
        if sharp and now - self.last_at > CLAP_MIN_GAP:
            if DEBUG:
                log(f"짝! peak={peak:.2f} (기준 {threshold:.2f})")
            if self.first_at and now - self.first_at <= CLAP_MAX_GAP:
                hit = True
                self.first_at = 0.0
            else:
                self.first_at = now
            self.last_at = now
        self.loud_blocks = self.loud_blocks + 1 if peak > threshold else 0
        if self.loud_blocks > 6:
            self.first_at = 0.0
        self.noise = 0.995 * self.noise + 0.005 * min(peak, threshold)
        self.prev_peak = peak
        return hit


def load_wakeword():
    try:
        import openwakeword
        from openwakeword.model import Model
        try:
            openwakeword.utils.download_models(model_names=[WAKE_MODEL_NAME])
        except Exception:
            pass
        try:
            return Model(wakeword_models=[WAKE_MODEL_NAME], inference_framework="onnx")
        except TypeError:
            return Model(wakeword_models=[WAKE_MODEL_NAME])
    except Exception as e:
        log(f'"Hey Jarvis" 모델을 못 불러와서 박수 2번만 씁니다. ({e})')
        return None


def run(on_wake=None, is_tab_open=None):
    import numpy as np
    import sounddevice as sd

    on_wake = on_wake or wake_jarvis
    is_tab_open = is_tab_open or (lambda: server_state() is True)

    oww = load_wakeword()
    clap = ClapDetector()
    buf = []
    last_wake = [0.0]
    tab_open = [False]
    last_check = [0.0]
    level = [0.0]

    def fire(reason):
        now = time.time()
        if now - last_wake[0] > COOLDOWN_SEC:
            last_wake[0] = now
            log(f"{reason} 감지!")
            on_wake(reason)

    def on_audio(indata, _frames, _t, _s):
        if tab_open[0]:
            return
        mono = np.clip(indata[:, 0] * MIC_GAIN, -1.0, 1.0)
        now = time.time()
        level[0] = max(level[0], float(np.max(np.abs(mono))))
        peak = float(np.max(np.abs(mono)))
        rms = float(np.sqrt(np.mean(mono * mono)) + 1e-9)
        if clap.feed(peak, rms, now):
            fire("박수 2번")
        if oww is not None:
            buf.append(mono.copy())
            if sum(len(b) for b in buf) >= OWW_CHUNK:
                chunk = np.concatenate(buf)
                buf.clear()
                try:
                    score = oww.predict((chunk * 32767).astype(np.int16)).get(WAKE_MODEL_NAME, 0.0)
                except Exception:
                    return
                if DEBUG and score > 0.05:
                    log(f"hey jarvis 점수 {score:.2f} (기준 {WAKE_THRESHOLD})")
                if score > WAKE_THRESHOLD:
                    oww.reset()
                    fire('"Hey Jarvis"')

    log('대기 중: 박수 2번 짝짝 또는 "Hey Jarvis" 라고 하면 자비스가 켜집니다.' if oww
        else "대기 중: 박수 2번 짝짝 치면 자비스가 켜집니다.")
    with sd.InputStream(channels=1, samplerate=SAMPLE_RATE, blocksize=BLOCK,
                        dtype="float32", callback=on_audio):
        while True:
            time.sleep(0.5)
            if DEBUG and not tab_open[0]:
                bar = "#" * int(min(level[0], 1.0) * 40)
                log(f"마이크 크기 {level[0]:.2f} {bar}")
            level[0] = 0.0
            if time.time() - last_check[0] > 2:
                last_check[0] = time.time()
                was = tab_open[0]
                tab_open[0] = bool(is_tab_open())
                if tab_open[0] and not was:
                    log("자비스 화면이 열려 있어서 쉬는 중이에요. (화면 탭을 닫으면 다시 박수/Hey Jarvis 대기)")
                if was and not tab_open[0]:
                    buf.clear()
                    if oww is not None:
                        oww.reset()


def startup_file():
    folder = os.path.join(os.environ.get("APPDATA", ""), r"Microsoft\Windows\Start Menu\Programs\Startup")
    return os.path.join(folder, "jarvis_wake.vbs")


def install():
    pyw = sys.executable
    if pyw.lower().endswith("python.exe"):
        cand = pyw[:-10] + "pythonw.exe"
        if os.path.exists(cand):
            pyw = cand
    script = os.path.join(BASE_DIR, "jarvis_wake.py")
    vbs = (f'Set s = CreateObject("WScript.Shell")\r\n'
           f's.CurrentDirectory = "{BASE_DIR}"\r\n'
           f's.Run """{pyw}"" ""{script}""", 0, False\r\n')
    with open(startup_file(), "w", encoding="utf-8") as f:
        f.write(vbs)
    subprocess.Popen([pyw, script], cwd=BASE_DIR)
    log("등록 완료! 지금부터, 그리고 컴퓨터를 켤 때마다 창 없이 조용히 대기합니다.")


def uninstall():
    try:
        os.remove(startup_file())
        log("자동 시작 등록을 지웠습니다. (지금 돌고 있는 건 작업 관리자에서 pythonw를 끄거나 재부팅하면 꺼집니다)")
    except FileNotFoundError:
        log("등록되어 있지 않습니다.")


def record_test():
    import wave
    import numpy as np
    import sounddevice as sd
    sr = SAMPLE_RATE
    parts = []
    for msg, sec in [("3초 뒤 시작합니다. 조용히 계세요...", 3),
                     ("지금 박수 2번! 짝짝 (잠깐 쉬고 한 번 더 짝짝)", 6),
                     ('지금 "헤이 자비스" 를 3번 말해 주세요 (평소 목소리로)', 8)]:
        print(">>> " + msg, flush=True)
        x = sd.rec(int(sr * sec), samplerate=sr, channels=1, dtype="float32")
        sd.wait()
        parts.append(x[:, 0])
        print(f"    (이 구간 가장 큰 소리: {float(np.max(np.abs(x))):.3f})", flush=True)
    audio = np.concatenate(parts)
    path = os.path.join(BASE_DIR, "wake_test.wav")
    with wave.open(path, "wb") as w:
        w.setnchannels(1)
        w.setsampwidth(2)
        w.setframerate(sr)
        w.writeframes((np.clip(audio, -1, 1) * 32767).astype(np.int16).tobytes())
    print(f"저장 완료: {path}  → Claude에게 '녹음했어' 라고 알려주세요.")


if __name__ == "__main__":
    if "--record" in sys.argv:
        record_test()
    elif "--install" in sys.argv:
        install()
    elif "--uninstall" in sys.argv:
        uninstall()
    else:
        try:
            run()
        except KeyboardInterrupt:
            pass
