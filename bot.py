import cv2
import pyautogui  # Solo para obtener info de pantalla si se necesitase
import time
import math
import numpy as np
import ctypes
from ctypes import wintypes
import tkinter as tk
from tkinter import messagebox

# Limpiar instancias Tk residuales (por si hubo KeyboardInterrupt previo)
try:
    _tk_temp = tk.Tk()
    _tk_temp.destroy()
    del _tk_temp
except:
    pass

# ==========================================
# --- CONFIGURACIÓN PRINCIPAL ---
# ==========================================
RUTA_IMAGEN = '78 Minimalist Tattoos That Will Inspire You To Get Inked.jpg'  # Ruta de la imagen a dibujar

VELOCIDAD_DIBUJADO = 0.01
NIVEL_SUAVIZADO = 3.0
PASO_ESCALA = 0.02    # Incremento de escala por cada paso de rueda
PASO_ROTACION = 5     # Grados por cada pulsación de R/L

# MODO DE TRAZO:
#   "contorno"  -> Extrae los bordes de cada trazo (doble línea en trazos gruesos)
#   "esqueleto" -> Reduce cada trazo a una sola línea central (esqueletización)
MODO_TRAZO = "esqueleto"

# NIVEL DE DETALLE:
#   "completo"  -> Todos los trazos, mínima simplificación
#   "medio"     -> Trazos moderados, simplificación media
#   "sencillo"  -> Solo trazos principales, simplificación agresiva
NIVEL_DETALLE = "completo"

# Umbral adaptativo
UMBRAL_ADAPTATIVO = True

# Mínimo de puntos para considerar un trazo válido (base, se ajusta con detalle)
MIN_PUNTOS_TRAZO = 15
MIN_PUNTOS_ESQUELETO = 2

# --- MODO MOSAICO (TILES) ---
FILAS_MOSAICO = 2       # Filas de la cuadrícula
COLS_MOSAICO = 2        # Columnas de la cuadrícula
# ==========================================

# --- Configuración de niveles de detalle ---
_DETALLE_CONFIG = {
    'completo': {
        'epsilon_esqueleto': 0.3,     # Multiplicador de NIVEL_SUAVIZADO para approxPolyDP
        'epsilon_contorno': 1.0,      # Multiplicador directo de NIVEL_SUAVIZADO
        'min_puntos_esqueleto': 2,
        'min_puntos_trazo': 15,
        'min_longitud_arco': 0,       # Mínima longitud de arco del contorno (0 = sin filtro)
    },
    'medio': {
        'epsilon_esqueleto': 0.8,
        'epsilon_contorno': 2.5,
        'min_puntos_esqueleto': 4,
        'min_puntos_trazo': 30,
        'min_longitud_arco': 20,
    },
    'sencillo': {
        'epsilon_esqueleto': 1.8,
        'epsilon_contorno': 5.0,
        'min_puntos_esqueleto': 6,
        'min_puntos_trazo': 50,
        'min_longitud_arco': 50,
    },
}

_CICLO_DETALLE = ['completo', 'medio', 'sencillo']

escala = 1.0
rotacion = 0        # Ángulo de rotación en grados
offset_x = 200
offset_y = 200

# ==========================================
# --- MOTOR DE RATÓN VIA SendInput (ctypes) ---
# ==========================================
INPUT_MOUSE = 0
MOUSEEVENTF_MOVE        = 0x0001
MOUSEEVENTF_LEFTDOWN    = 0x0002
MOUSEEVENTF_LEFTUP      = 0x0004
MOUSEEVENTF_ABSOLUTE    = 0x8000
MOUSEEVENTF_MOVE_NOCOALESCE = 0x2000

SM_CXSCREEN = 0
SM_CYSCREEN = 1

class MOUSEINPUT(ctypes.Structure):
    _fields_ = [
        ("dx",          ctypes.c_long),
        ("dy",          ctypes.c_long),
        ("mouseData",   ctypes.c_ulong),
        ("dwFlags",     ctypes.c_ulong),
        ("time",        ctypes.c_ulong),
        ("dwExtraInfo", ctypes.POINTER(ctypes.c_ulong)),
    ]

class INPUT(ctypes.Structure):
    class _UNION(ctypes.Union):
        _fields_ = [("mi", MOUSEINPUT)]
    _fields_ = [
        ("type", ctypes.c_ulong),
        ("ii",   _UNION),
    ]

_user32 = ctypes.windll.user32
_screen_w = _user32.GetSystemMetrics(SM_CXSCREEN)
_screen_h = _user32.GetSystemMetrics(SM_CYSCREEN)

def _send_mouse_event(dx, dy, flags):
    extra = ctypes.c_ulong(0)
    inp = INPUT()
    inp.type = INPUT_MOUSE
    inp.ii.mi.dx = dx
    inp.ii.mi.dy = dy
    inp.ii.mi.mouseData = 0
    inp.ii.mi.dwFlags = flags
    inp.ii.mi.time = 0
    inp.ii.mi.dwExtraInfo = ctypes.pointer(extra)
    _user32.SendInput(1, ctypes.pointer(inp), ctypes.sizeof(INPUT))

def mover_mouse_abs(x, y):
    nx = int(x * 65535 / (_screen_w - 1))
    ny = int(y * 65535 / (_screen_h - 1))
    _send_mouse_event(
        nx, ny,
        MOUSEEVENTF_MOVE | MOUSEEVENTF_ABSOLUTE | MOUSEEVENTF_MOVE_NOCOALESCE
    )

def mouse_down():
    _send_mouse_event(0, 0, MOUSEEVENTF_LEFTDOWN)

def mouse_up():
    _send_mouse_event(0, 0, MOUSEEVENTF_LEFTUP)

def obtener_pos_cursor():
    pt = wintypes.POINT()
    _user32.GetCursorPos(ctypes.byref(pt))
    return pt.x, pt.y

# ==========================================
# --- DETECCION DE TECLAS (GetAsyncKeyState) ---
# ==========================================
VK_SPACE = 0x20
VK_ESCAPE = 0x1B
VK_V = 0x56

def _tecla_recien_pulsada(vk_code):
    """Detecta si una tecla fue pulsada desde la ultima comprobacion."""
    return _user32.GetAsyncKeyState(vk_code) & 1 != 0


# ==========================================
# --- OVERLAY DE PROGRESO ---
# ==========================================
class OverlayDibujo:
    """Ventana overlay compacta en la esquina superior izquierda.
    Muestra estado (dibujando/pausa), trazos restantes, tiempo restante.
    Controles: ESPACIO=Pausar/Reanudar, V=Vista previa (en pausa), ESC=Cancelar."""

    def __init__(self, total_trazos, total_puntos):
        self.total_trazos = total_trazos
        self.total_puntos = total_puntos
        self.trazos_completados = 0
        self.puntos_dibujados = 0
        self.t_inicio = time.time()
        self.pausado = False
        self.cancelado = False
        self.solicitar_preview = False

        self.root = tk.Tk()
        self.root.title("")
        self.root.attributes('-topmost', True)
        self.root.attributes('-alpha', 0.88)
        self.root.overrideredirect(True)
        self.root.geometry("+10+10")
        self.root.configure(bg='#1e1e2e')

        self._crear_ui()
        self.root.update()

    def _crear_ui(self):
        pad = {'padx': 10, 'pady': 2}
        bg = '#1e1e2e'

        self.lbl_estado = tk.Label(self.root, text="\u25cf DIBUJANDO",
                                    font=("Consolas", 14, "bold"),
                                    fg="#4CAF50", bg=bg)
        self.lbl_estado.pack(**pad, anchor='w')

        sep1 = tk.Frame(self.root, height=1, bg='#444444')
        sep1.pack(fill='x', padx=8, pady=2)

        self.lbl_trazos = tk.Label(self.root, text="Trazos: 0 / 0",
                                    font=("Consolas", 11), fg="white", bg=bg)
        self.lbl_trazos.pack(**pad, anchor='w')

        self.lbl_puntos = tk.Label(self.root, text="Puntos: 0 / 0",
                                    font=("Consolas", 10), fg="#AAAAAA", bg=bg)
        self.lbl_puntos.pack(**pad, anchor='w')

        self.lbl_restante = tk.Label(self.root, text="Restante: --",
                                      font=("Consolas", 11), fg="#FFD700", bg=bg)
        self.lbl_restante.pack(**pad, anchor='w')

        self.lbl_transcurrido = tk.Label(self.root, text="Transcurrido: 0s",
                                          font=("Consolas", 10), fg="#888888", bg=bg)
        self.lbl_transcurrido.pack(**pad, anchor='w')

        sep2 = tk.Frame(self.root, height=1, bg='#444444')
        sep2.pack(fill='x', padx=8, pady=4)

        self.lbl_teclas = tk.Label(self.root,
                                    text="ESPACIO: Pausar\nESC: Cancelar",
                                    font=("Consolas", 9), fg="#888888", bg=bg,
                                    justify='left')
        self.lbl_teclas.pack(padx=10, pady=(0, 8), anchor='w')

    def actualizar(self, trazos_hechos, puntos_hechos):
        """Actualiza el overlay. Llamar periodicamente desde el bucle de dibujo."""
        self.trazos_completados = trazos_hechos
        self.puntos_dibujados = puntos_hechos

        restantes_t = self.total_trazos - trazos_hechos
        restantes_p = self.total_puntos - puntos_hechos

        t_transcurrido = time.time() - self.t_inicio

        # Estimar tiempo restante basado en velocidad real
        if puntos_hechos > 10:
            vel_real = t_transcurrido / puntos_hechos
            t_restante = restantes_p * vel_real + restantes_t * 0.15
        else:
            t_restante = restantes_p * VELOCIDAD_DIBUJADO + restantes_t * 0.15

        # Estado
        if self.pausado:
            self.lbl_estado.config(text="\u23f8 PAUSA", fg="#FF9800")
            self.lbl_teclas.config(text="ESPACIO: Continuar\nV: Vista previa\nESC: Cancelar")
        else:
            self.lbl_estado.config(text="\u25cf DIBUJANDO", fg="#4CAF50")
            self.lbl_teclas.config(text="ESPACIO: Pausar\nESC: Cancelar")

        self.lbl_trazos.config(
            text=f"Trazos: {trazos_hechos}/{self.total_trazos}  (quedan {restantes_t})")
        self.lbl_puntos.config(
            text=f"Puntos: {puntos_hechos}/{self.total_puntos}")
        self.lbl_restante.config(
            text=f"Restante: ~{_formato_tiempo(t_restante)}")
        self.lbl_transcurrido.config(
            text=f"Transcurrido: {_formato_tiempo(t_transcurrido)}")

        try:
            self.root.update_idletasks()
            self.root.update()
        except tk.TclError:
            pass

    def verificar_teclas(self):
        """Comprueba teclas de control. Llamar frecuentemente."""
        if _tecla_recien_pulsada(VK_SPACE):
            self.pausado = not self.pausado
            time.sleep(0.15)  # Debounce
        if _tecla_recien_pulsada(VK_ESCAPE):
            self.cancelado = True
        if self.pausado and _tecla_recien_pulsada(VK_V):
            self.solicitar_preview = True

    def esperar_reanudacion(self, trazos_hechos, puntos_hechos):
        """Bucle de espera mientras esta pausado.
        Retorna: 'continuar', 'preview' o 'cancelar'."""
        while self.pausado and not self.cancelado:
            self.verificar_teclas()
            self.actualizar(trazos_hechos, puntos_hechos)

            if self.solicitar_preview:
                self.solicitar_preview = False
                return 'preview'

            time.sleep(0.05)

        return 'continuar' if not self.cancelado else 'cancelar'

    def cerrar(self):
        try:
            self.root.destroy()
        except:
            pass


# ==========================================
# --- ESQUELETIZACIÓN ---
# ==========================================
def esqueletizar(img_binaria):
    try:
        esqueleto = cv2.ximgproc.thinning(img_binaria, thinningType=cv2.ximgproc.THINNING_ZHANGSUEN)
        print("  (Esqueletización: cv2.ximgproc.thinning - rápido)")
        return esqueleto
    except AttributeError:
        pass

    print("  (Esqueletización: Zhang-Suen manual - puede tardar unos segundos...)")
    imagen = (img_binaria > 0).astype(np.uint8)

    while True:
        marcados1 = _zhang_suen_iter(imagen, 0)
        imagen = imagen & (~marcados1).astype(np.uint8)
        marcados2 = _zhang_suen_iter(imagen, 1)
        imagen = imagen & (~marcados2).astype(np.uint8)
        if np.sum(marcados1) == 0 and np.sum(marcados2) == 0:
            break

    return (imagen * 255).astype(np.uint8)


def _zhang_suen_iter(img, paso):
    marcados = np.zeros_like(img)
    h, w = img.shape
    for y in range(1, h - 1):
        for x in range(1, w - 1):
            if img[y, x] != 1:
                continue
            P2 = img[y-1, x]
            P3 = img[y-1, x+1]
            P4 = img[y, x+1]
            P5 = img[y+1, x+1]
            P6 = img[y+1, x]
            P7 = img[y+1, x-1]
            P8 = img[y, x-1]
            P9 = img[y-1, x-1]
            vecinos = [P2, P3, P4, P5, P6, P7, P8, P9]

            B = sum(vecinos)
            if B < 2 or B > 6:
                continue

            s = [P2, P3, P4, P5, P6, P7, P8, P9, P2]
            A = sum(1 for i in range(8) if s[i] == 0 and s[i+1] == 1)
            if A != 1:
                continue

            if paso == 0:
                if P2 * P4 * P6 != 0:
                    continue
                if P4 * P6 * P8 != 0:
                    continue
            else:
                if P2 * P4 * P8 != 0:
                    continue
                if P2 * P6 * P8 != 0:
                    continue

            marcados[y, x] = 1
    return marcados


# ==========================================
# --- TRAZADO DIRECTO DEL ESQUELETO ---
# ==========================================
def _extraer_trazos_esqueleto(esqueleto):
    """Extrae trazos como cadenas de píxeles directamente del esqueleto (1px).
    Produce una sola línea por trazo en lugar de los contornos dobles
    que genera findContours sobre una imagen dilatada."""
    h, w = esqueleto.shape
    skel = (esqueleto > 0).astype(np.uint8)

    # Contar vecinos de cada píxel (8-connectivity) con filtro rápido
    kernel_vec = np.ones((3, 3), dtype=np.uint8)
    kernel_vec[1, 1] = 0
    num_vecinos = cv2.filter2D(skel, -1, kernel_vec)
    num_vecinos = num_vecinos * skel  # solo píxeles del esqueleto

    # Endpoints: píxeles con exactamente 1 vecino (puntas de línea)
    ey, ex = np.where((num_vecinos == 1) & (skel > 0))
    endpoints = list(zip(ey.tolist(), ex.tolist()))

    visitado = np.zeros((h, w), dtype=bool)
    trazos = []

    dx8 = [-1, -1, -1, 0, 0, 1, 1, 1]
    dy8 = [-1, 0, 1, -1, 1, -1, 0, 1]

    def trazar_desde(sy, sx):
        """Sigue los píxeles conectados desde (sy,sx) hasta que no haya más."""
        path = [(sx, sy)]
        visitado[sy, sx] = True
        cy, cx = sy, sx
        while True:
            siguiente = None
            for ddx, ddy in zip(dx8, dy8):
                nx, ny = cx + ddx, cy + ddy
                if 0 <= nx < w and 0 <= ny < h and skel[ny, nx] > 0 and not visitado[ny, nx]:
                    siguiente = (ny, nx)
                    break
            if siguiente is None:
                break
            ny, nx = siguiente
            path.append((nx, ny))
            visitado[ny, nx] = True
            cy, cx = ny, nx
        return path

    # 1) Trazar desde endpoints (líneas abiertas)
    for epy, epx in endpoints:
        if visitado[epy, epx]:
            continue
        path = trazar_desde(epy, epx)
        if len(path) >= 2:
            contour = np.array([[[p[0], p[1]]] for p in path], dtype=np.int32)
            trazos.append(contour)

    # 2) Trazar loops cerrados restantes (píxeles no visitados)
    ys_rest, xs_rest = np.where((skel > 0) & (~visitado))
    for ry, rx in zip(ys_rest.tolist(), xs_rest.tolist()):
        if visitado[ry, rx]:
            continue
        path = trazar_desde(ry, rx)
        if len(path) >= 2:
            contour = np.array([[[p[0], p[1]]] for p in path], dtype=np.int32)
            trazos.append(contour)

    print(f"  (Trazado directo del esqueleto: {len(trazos)} trazos, línea única)")
    return trazos


# ==========================================
# --- PROCESAMIENTO DE IMAGEN ---
# ==========================================
def extraer_coordenadas_negras(ruta_imagen, modo=None, detalle=None):
    """Extrae trazos de la imagen. Devuelve (trazos, tiempo_segundos).
    detalle: 'completo', 'medio', 'sencillo' — controla agresividad de simplificación."""
    if modo is None:
        modo = MODO_TRAZO
    if detalle is None:
        detalle = NIVEL_DETALLE

    cfg = _DETALLE_CONFIG.get(detalle, _DETALLE_CONFIG['completo'])

    t_inicio = time.time()
    print(f"Analizando la imagen (modo: {modo}, detalle: {detalle})...")
    img = cv2.imread(ruta_imagen, cv2.IMREAD_GRAYSCALE)
    if img is None:
        print(f"❌ Error: No se pudo cargar '{ruta_imagen}'.")
        return [], 0.0

    if UMBRAL_ADAPTATIVO:
        img_blur = cv2.GaussianBlur(img, (5, 5), 0)
        umbral_invertido = cv2.adaptiveThreshold(
            img_blur, 255,
            cv2.ADAPTIVE_THRESH_GAUSSIAN_C,
            cv2.THRESH_BINARY_INV,
            blockSize=15, C=10
        )
        kernel_limpieza = np.ones((2, 2), np.uint8)
        umbral_invertido = cv2.morphologyEx(umbral_invertido, cv2.MORPH_OPEN, kernel_limpieza)
        print("  (Umbral: adaptativo gaussiano)")
    else:
        _, umbral_invertido = cv2.threshold(img, 200, 255, cv2.THRESH_BINARY_INV)
        print("  (Umbral: fijo 200)")

    if modo == "esqueleto":
        print("  Aplicando esqueletización (línea central)...")
        esqueleto = esqueletizar(umbral_invertido)

        # Trazado directo del esqueleto (1 línea por trazo, sin dilatar)
        contornos = _extraer_trazos_esqueleto(esqueleto)

        epsilon_val = max(NIVEL_SUAVIZADO * cfg['epsilon_esqueleto'], 0.4)
        min_pts = cfg['min_puntos_esqueleto']
        min_arco = cfg['min_longitud_arco']

        trazos_suavizados = []
        for c in contornos:
            if len(c) < min_pts:
                continue
            if min_arco > 0 and cv2.arcLength(c, False) < min_arco:
                continue
            suave = cv2.approxPolyDP(c, epsilon_val, False)
            if len(suave) >= 2:
                trazos_suavizados.append(suave)

        trazos_suavizados = _ordenar_trazos_espacial(trazos_suavizados)

        t_total = time.time() - t_inicio
        print(f"✅ {len(trazos_suavizados)} trazos (esqueleto/{detalle}) en {t_total:.2f}s")
        return trazos_suavizados, t_total

    else:
        contornos, _ = cv2.findContours(umbral_invertido, cv2.RETR_LIST, cv2.CHAIN_APPROX_NONE)

        epsilon_val = NIVEL_SUAVIZADO * cfg['epsilon_contorno']
        min_pts = cfg['min_puntos_trazo']
        min_arco = cfg['min_longitud_arco']

        trazos_suavizados = []
        for c in contornos:
            if len(c) < min_pts:
                continue
            if min_arco > 0 and cv2.arcLength(c, False) < min_arco:
                continue
            contorno_suave = cv2.approxPolyDP(c, epsilon_val, False)
            if len(contorno_suave) >= 2:
                trazos_suavizados.append(contorno_suave)

        trazos_suavizados = _ordenar_trazos_espacial(trazos_suavizados)

        t_total = time.time() - t_inicio
        print(f"✅ {len(trazos_suavizados)} trazos (contorno/{detalle}) en {t_total:.2f}s")
        return trazos_suavizados, t_total


# ==========================================
# --- UTILIDADES ---
# ==========================================
def _contar_puntos(trazos):
    return sum(len(c) for c in trazos)

def _estimar_tiempo_dibujo(trazos):
    total_puntos = _contar_puntos(trazos)
    return total_puntos * VELOCIDAD_DIBUJADO + len(trazos) * 0.15

def _formato_tiempo(segundos):
    s = int(segundos)
    if s < 60:
        return f"{s}s"
    elif s < 3600:
        return f"{s // 60}m {s % 60:02d}s"
    else:
        return f"{s // 3600}h {(s % 3600) // 60:02d}m {s % 60:02d}s"

def _ordenar_trazos_espacial(trazos):
    """Ordena los trazos de arriba-abajo, izquierda-derecha."""
    if not trazos:
        return trazos
    centroides = []
    for c in trazos:
        xs = [p[0][0] for p in c]
        ys = [p[0][1] for p in c]
        centroides.append((sum(xs) / len(xs), sum(ys) / len(ys)))
    min_y = min(cy for _, cy in centroides)
    max_y = max(cy for _, cy in centroides)
    rango_y = max_y - min_y if max_y > min_y else 1
    n_bandas = 20
    alto_banda = rango_y / n_bandas
    def clave_orden(idx):
        cx, cy = centroides[idx]
        banda = int((cy - min_y) / alto_banda) if alto_banda > 0 else 0
        return (banda, cx)
    indices_ordenados = sorted(range(len(trazos)), key=clave_orden)
    return [trazos[i] for i in indices_ordenados]

def _calcular_centro(trazos):
    todos_x, todos_y = [], []
    for c in trazos:
        for p in c:
            todos_x.append(p[0][0])
            todos_y.append(p[0][1])
    if not todos_x:
        return 0, 0
    return (min(todos_x) + max(todos_x)) / 2, (min(todos_y) + max(todos_y)) / 2

def _calcular_bbox(trazos):
    todos_x = [p[0][0] for c in trazos for p in c]
    todos_y = [p[0][1] for c in trazos for p in c]
    if not todos_x:
        return 0, 0, 0, 0
    return min(todos_x), min(todos_y), max(todos_x), max(todos_y)

def _transformar_punto(px, py, cx_img, cy_img):
    dx = (px - cx_img) * escala
    dy = (py - cy_img) * escala
    rad = math.radians(rotacion)
    cos_a, sin_a = math.cos(rad), math.sin(rad)
    rx = dx * cos_a - dy * sin_a
    ry = dx * sin_a + dy * cos_a
    return int(offset_x + rx), int(offset_y + ry)

def _obtener_tile_de_punto(px, py, min_x, min_y, ancho_tile, alto_tile, cols, filas):
    c = int((px - min_x) / ancho_tile)
    f = int((py - min_y) / alto_tile)
    c = max(0, min(c, cols - 1))
    f = max(0, min(f, filas - 1))
    return f * cols + c + 1

def _agrupar_trazos_por_tile(trazos, filas, cols):
    """Agrupa los trazos RECORTANDO cada trazo en los límites del tile.
    Cada tile solo contiene los segmentos de trazos que caen dentro de su rectángulo.
    Retorna dict: {tile_num: [trazos]}  (tile_num 1-based)"""
    if not trazos:
        return {}
    min_x, min_y, max_x, max_y = _calcular_bbox(trazos)
    ancho = max_x - min_x
    alto = max_y - min_y
    if ancho == 0 or alto == 0:
        return {1: trazos}
    ancho_tile = ancho / cols
    alto_tile = alto / filas

    grupos = {}
    for f in range(filas):
        for c in range(cols):
            tile_num = f * cols + c + 1
            # Rectángulo del tile con pequeño margen para evitar huecos
            margen = max(ancho_tile, alto_tile) * 0.01
            tx1 = min_x + c * ancho_tile - margen
            ty1 = min_y + f * alto_tile - margen
            tx2 = min_x + (c + 1) * ancho_tile + margen
            ty2 = min_y + (f + 1) * alto_tile + margen
            # Recortar trazos punto a punto dentro de este rectángulo
            trazos_recortados = _filtrar_trazos_tile(trazos, tx1, ty1, tx2, ty2)
            if trazos_recortados:
                grupos[tile_num] = trazos_recortados
    return grupos


# ==========================================
# --- MOSAICO (TILES) ---
# ==========================================
def _filtrar_trazos_tile(trazos, x1, y1, x2, y2):
    """Recorta trazos punto a punto: solo mantiene los puntos dentro del rectángulo.
    Si un trazo sale del rectángulo, se corta y se crean segmentos separados."""
    resultado = []
    for contorno in trazos:
        segmento_actual = []
        for p in contorno:
            px, py = p[0][0], p[0][1]
            if x1 <= px <= x2 and y1 <= py <= y2:
                segmento_actual.append(p)
            else:
                if len(segmento_actual) >= 2:
                    resultado.append(np.array(segmento_actual))
                segmento_actual = []
        if len(segmento_actual) >= 2:
            resultado.append(np.array(segmento_actual))
    return resultado

def _dividir_en_tiles(trazos, filas, cols):
    min_x, min_y, max_x, max_y = _calcular_bbox(trazos)
    ancho = max_x - min_x
    alto = max_y - min_y
    if ancho == 0 or alto == 0:
        return []
    ancho_tile = ancho / cols
    alto_tile = alto / filas
    margen = max(ancho_tile, alto_tile) * 0.03

    tiles = []
    for f in range(filas):
        for c in range(cols):
            tx1 = min_x + c * ancho_tile - margen
            ty1 = min_y + f * alto_tile - margen
            tx2 = min_x + (c + 1) * ancho_tile + margen
            ty2 = min_y + (f + 1) * alto_tile + margen
            trazos_tile = _filtrar_trazos_tile(trazos, tx1, ty1, tx2, ty2)
            tiles.append((f, c, trazos_tile, (tx1, ty1, tx2, ty2)))
    return tiles


# ==========================================
# --- COLORES POR TILE ---
# ==========================================
_COLORES_TILE = [
    "#2196F3",  # azul
    "#F44336",  # rojo
    "#4CAF50",  # verde
    "#FF9800",  # naranja
    "#9C27B0",  # púrpura
    "#00BCD4",  # cyan
    "#E91E63",  # rosa
    "#795548",  # marrón
    "#607D8B",  # gris azulado
]


# ==========================================
# --- INTERFAZ DE AJUSTE (Tkinter) ---
# ==========================================
def mostrar_interfaz_ajustable(contornos, tiempo_procesado, ruta_imagen, tile_info=None):
    """Muestra la interfaz de preview/posicionamiento.
    Retorna dict: {'iniciar': bool, 'contornos': list, 'usar_tiles': bool}"""
    global escala, rotacion, offset_x, offset_y, MODO_TRAZO, NIVEL_DETALLE
    global FILAS_MOSAICO, COLS_MOSAICO

    resultado = {
        'iniciar': False,
        'contornos': contornos,
        'usar_tiles': False,
    }

    root = tk.Tk()
    root.title("Dibujo Bot — Ajuste de posición")
    root.attributes('-topmost', True)
    root.attributes('-alpha', 0.6)

    ancho_pantalla = root.winfo_screenwidth()
    alto_pantalla = root.winfo_screenheight()
    root.attributes('-fullscreen', True)

    canvas = tk.Canvas(root, width=ancho_pantalla, height=alto_pantalla, bg='white', highlightthickness=0)
    canvas.pack()

    root.start_x = 0
    root.start_y = 0

    cache = {
        (MODO_TRAZO, NIVEL_DETALLE): (contornos, tiempo_procesado),
    }
    estado = {
        'contornos': contornos,
        't_procesado': tiempo_procesado,
        'procesando': False,
        'mostrar_grid': False,
    }

    def actualizar_canvas():
        canvas.delete("all")

        teclas_l1 = "Rueda: Escalar | Arrastrar: Mover | R/L: Rotar"
        if tile_info is None:
            teclas_l1 += " | Z: Modo | D: Detalle"
        teclas_l1 += " | ENTER: Dibujar | ESC: Cancelar"
        canvas.create_text(ancho_pantalla // 2, 22, text=teclas_l1,
                           font=("Arial", 13, "bold"), fill="red")

        if tile_info is None:
            teclas_l2 = f"T: Grid/Tiles | +/-: Tamaño grid ({FILAS_MOSAICO}x{COLS_MOSAICO})"
            canvas.create_text(ancho_pantalla // 2, 44, text=teclas_l2,
                               font=("Arial", 12, "bold"), fill="#666666")

        # Indicador de modo tiles
        if estado['mostrar_grid'] and tile_info is None:
            canvas.create_text(ancho_pantalla // 2, 100,
                               text=f"⬛ MODO TILES ACTIVO ({FILAS_MOSAICO}x{COLS_MOSAICO} = {FILAS_MOSAICO * COLS_MOSAICO} tiles) — Dibujará tile por tile con pausas",
                               font=("Arial", 13, "bold"), fill="#E91E63")

        n_trazos = len(estado['contornos'])
        n_puntos = _contar_puntos(estado['contornos'])
        t_proc = _formato_tiempo(estado['t_procesado'])
        t_dibujo_est = _formato_tiempo(_estimar_tiempo_dibujo(estado['contornos']))
        rot_txt = f"{rotacion}°"
        detalle_emoji = {"completo": "🔴", "medio": "🟡", "sencillo": "🟢"}.get(NIVEL_DETALLE, "")
        info = (f"Escala: {escala:.2f}x | Rot: {rot_txt} | {MODO_TRAZO} | "
                f"{detalle_emoji} {NIVEL_DETALLE} | "
                f"Trazos: {n_trazos} ({n_puntos} pts) | "
                f"Proc: {t_proc} | Dibujo: ~{t_dibujo_est}")
        if tile_info is not None:
            tile_num, tile_total, _ = tile_info
            info = f"TILE {tile_num}/{tile_total} | " + info
        canvas.create_text(ancho_pantalla // 2, 68, text=info,
                           font=("Arial", 13), fill="black")

        if estado['procesando']:
            canvas.create_text(ancho_pantalla // 2, alto_pantalla // 2,
                               text="Procesando imagen...",
                               font=("Arial", 28, "bold"), fill="orange")
            return

        cx_img, cy_img = _calcular_centro(estado['contornos'])
        inicio_x, inicio_y = None, None

        # Decidir si colorear por tile (con recorte real punto a punto)
        colorear_por_tile = estado['mostrar_grid'] and tile_info is None and estado['contornos']

        if colorear_por_tile:
            # Usar el mismo recorte real que usa el dibujo: _agrupar_trazos_por_tile
            grupos_preview = _agrupar_trazos_por_tile(estado['contornos'], FILAS_MOSAICO, COLS_MOSAICO)
            total_t = FILAS_MOSAICO * COLS_MOSAICO
            first_drawn = True
            for t_num in range(1, total_t + 1):
                trazos_de_tile = grupos_preview.get(t_num, [])
                color = _COLORES_TILE[(t_num - 1) % len(_COLORES_TILE)]
                for contorno in trazos_de_tile:
                    puntos_planos = []
                    for punto in contorno:
                        px, py = _transformar_punto(punto[0][0], punto[0][1], cx_img, cy_img)
                        puntos_planos.extend([px, py])
                        if first_drawn and inicio_x is None:
                            inicio_x, inicio_y = px, py
                    if len(puntos_planos) >= 4:
                        canvas.create_line(puntos_planos, fill=color, width=2)
                if trazos_de_tile:
                    first_drawn = False
        else:
            # Modo normal: todo azul
            for i, contorno in enumerate(estado['contornos']):
                puntos_planos = []
                for punto in contorno:
                    px, py = _transformar_punto(punto[0][0], punto[0][1], cx_img, cy_img)
                    puntos_planos.extend([px, py])
                    if i == 0 and inicio_x is None:
                        inicio_x, inicio_y = px, py
                if len(puntos_planos) >= 4:
                    canvas.create_line(puntos_planos, fill="blue", width=2)

        if inicio_x is not None and inicio_y is not None:
            canvas.create_oval(inicio_x - 5, inicio_y - 5, inicio_x + 5, inicio_y + 5,
                               fill="red", outline="red")

        if estado['mostrar_grid'] and tile_info is None and estado['contornos']:
            _dibujar_grid_overlay(canvas, estado['contornos'], cx_img, cy_img)

    def _dibujar_grid_overlay(cv, trazos, cx_img, cy_img):
        min_x, min_y, max_x, max_y = _calcular_bbox(trazos)
        ancho_img = max_x - min_x
        alto_img = max_y - min_y
        if ancho_img == 0 or alto_img == 0:
            return
        filas = FILAS_MOSAICO
        cols = COLS_MOSAICO
        ancho_tile = ancho_img / cols
        alto_tile = alto_img / filas

        for c in range(cols + 1):
            px_img = min_x + c * ancho_tile
            sx_top, sy_top = _transformar_punto(px_img, min_y, cx_img, cy_img)
            sx_bot, sy_bot = _transformar_punto(px_img, max_y, cx_img, cy_img)
            cv.create_line(sx_top, sy_top, sx_bot, sy_bot, fill="white", width=3)
            cv.create_line(sx_top, sy_top, sx_bot, sy_bot, fill="black", width=1, dash=(6, 4))

        for f in range(filas + 1):
            py_img = min_y + f * alto_tile
            sx_lft, sy_lft = _transformar_punto(min_x, py_img, cx_img, cy_img)
            sx_rgt, sy_rgt = _transformar_punto(max_x, py_img, cx_img, cy_img)
            cv.create_line(sx_lft, sy_lft, sx_rgt, sy_rgt, fill="white", width=3)
            cv.create_line(sx_lft, sy_lft, sx_rgt, sy_rgt, fill="black", width=1, dash=(6, 4))

        num = 1
        for f in range(filas):
            for c_idx in range(cols):
                cx_t = min_x + (c_idx + 0.5) * ancho_tile
                cy_t = min_y + (f + 0.5) * alto_tile
                sx, sy = _transformar_punto(cx_t, cy_t, cx_img, cy_img)
                tile_color = _COLORES_TILE[(num - 1) % len(_COLORES_TILE)]
                cv.create_text(sx + 1, sy + 1, text=str(num),
                               font=("Arial", 26, "bold"), fill="white")
                cv.create_text(sx, sy, text=str(num),
                               font=("Arial", 26, "bold"), fill=tile_color)
                num += 1

    def hacer_zoom(event):
        global escala
        if hasattr(event, 'delta') and event.delta > 0:
            escala += PASO_ESCALA
        elif hasattr(event, 'num') and event.num == 4:
            escala += PASO_ESCALA
        else:
            escala = max(0.02, escala - PASO_ESCALA)
        escala = round(escala, 2)
        actualizar_canvas()

    def iniciar_arrastre(event):
        root.start_x = event.x
        root.start_y = event.y

    def arrastrar(event):
        global offset_x, offset_y
        dx = event.x - root.start_x
        dy = event.y - root.start_y
        offset_x += dx
        offset_y += dy
        root.start_x = event.x
        root.start_y = event.y
        actualizar_canvas()

    def rotar_horario(event):
        global rotacion
        rotacion = (rotacion + PASO_ROTACION) % 360
        actualizar_canvas()

    def rotar_antihorario(event):
        global rotacion
        rotacion = (rotacion - PASO_ROTACION) % 360
        actualizar_canvas()

    def _reprocesar_imagen():
        """Reprocesa la imagen con el modo y detalle actuales (con caché)."""
        cache_key = (MODO_TRAZO, NIVEL_DETALLE)
        if cache_key in cache:
            trazos_cached, t_cached = cache[cache_key]
            estado['contornos'] = trazos_cached
            estado['t_procesado'] = t_cached
            resultado['contornos'] = trazos_cached
            print(f"  (Cargado desde caché: {MODO_TRAZO}/{NIVEL_DETALLE})")
            actualizar_canvas()
            return

        estado['procesando'] = True
        actualizar_canvas()
        import threading
        def _worker():
            nuevos_trazos, t = extraer_coordenadas_negras(ruta_imagen, MODO_TRAZO, NIVEL_DETALLE)
            cache[cache_key] = (nuevos_trazos, t)
            estado['contornos'] = nuevos_trazos
            estado['t_procesado'] = t
            resultado['contornos'] = nuevos_trazos
            estado['procesando'] = False
            root.after(0, actualizar_canvas)
        threading.Thread(target=_worker, daemon=True).start()

    def cambiar_modo(event):
        global MODO_TRAZO
        if estado['procesando'] or tile_info is not None:
            return
        MODO_TRAZO = "contorno" if MODO_TRAZO == "esqueleto" else "esqueleto"
        _reprocesar_imagen()

    def cambiar_detalle(event):
        global NIVEL_DETALLE
        if estado['procesando'] or tile_info is not None:
            return
        idx = _CICLO_DETALLE.index(NIVEL_DETALLE) if NIVEL_DETALLE in _CICLO_DETALLE else 0
        NIVEL_DETALLE = _CICLO_DETALLE[(idx + 1) % len(_CICLO_DETALLE)]
        print(f"  Detalle → {NIVEL_DETALLE}")
        _reprocesar_imagen()

    def toggle_grid(event):
        if tile_info is not None:
            return
        estado['mostrar_grid'] = not estado['mostrar_grid']
        actualizar_canvas()

    def aumentar_grid(event):
        global FILAS_MOSAICO, COLS_MOSAICO
        if tile_info is not None:
            return
        if FILAS_MOSAICO < 6 or COLS_MOSAICO < 6:
            FILAS_MOSAICO = min(FILAS_MOSAICO + 1, 6)
            COLS_MOSAICO = min(COLS_MOSAICO + 1, 6)
            print(f"  Grid → {FILAS_MOSAICO}x{COLS_MOSAICO}")
            actualizar_canvas()

    def disminuir_grid(event):
        global FILAS_MOSAICO, COLS_MOSAICO
        if tile_info is not None:
            return
        if FILAS_MOSAICO > 1 or COLS_MOSAICO > 1:
            FILAS_MOSAICO = max(FILAS_MOSAICO - 1, 1)
            COLS_MOSAICO = max(COLS_MOSAICO - 1, 1)
            print(f"  Grid → {FILAS_MOSAICO}x{COLS_MOSAICO}")
            actualizar_canvas()

    def aceptar(event):
        if estado['procesando']:
            return
        resultado['iniciar'] = True
        resultado['contornos'] = estado['contornos']
        resultado['usar_tiles'] = estado['mostrar_grid']
        print(f">>> ENTER pulsado - iniciar dibujo (tiles={'SÍ' if estado['mostrar_grid'] else 'NO'})")
        root.quit()
        root.destroy()

    def cancelar(event):
        resultado['iniciar'] = False
        print(">>> ESC pulsado - cancelar")
        root.quit()
        root.destroy()

    root.bind("<MouseWheel>", hacer_zoom)
    root.bind("<Button-4>", hacer_zoom)
    root.bind("<Button-5>", hacer_zoom)
    root.bind("<ButtonPress-1>", iniciar_arrastre)
    root.bind("<B1-Motion>", arrastrar)
    root.bind("<r>", rotar_horario)
    root.bind("<R>", rotar_horario)
    root.bind("<l>", rotar_antihorario)
    root.bind("<L>", rotar_antihorario)
    root.bind("<z>", cambiar_modo)
    root.bind("<Z>", cambiar_modo)
    root.bind("<d>", cambiar_detalle)
    root.bind("<D>", cambiar_detalle)
    root.bind("<t>", toggle_grid)
    root.bind("<T>", toggle_grid)
    root.bind("<plus>", aumentar_grid)
    root.bind("<equal>", aumentar_grid)
    root.bind("<KP_Add>", aumentar_grid)
    root.bind("<minus>", disminuir_grid)
    root.bind("<KP_Subtract>", disminuir_grid)
    root.bind("<Return>", aceptar)
    root.bind("<Escape>", cancelar)

    actualizar_canvas()
    root.mainloop()

    print(f">>> mainloop terminó. iniciar={resultado['iniciar']}, tiles={resultado['usar_tiles']}")
    return resultado


# ==========================================
# --- PREVIEW DE TILE (entre tiles) ---
# ==========================================
def mostrar_preview_tile(trazos_tile, tile_num, total_tiles, todos_contornos, grupos):
    """Muestra preview entre tiles: trazos del tile actual resaltados,
    tiles ya hechos en gris, futuros en gris claro.
    El usuario puede mover/escalar para ajustar posición.
    Retorna dict: {'iniciar': bool}"""
    global escala, rotacion, offset_x, offset_y

    resultado = {'iniciar': False}

    root = tk.Tk()
    root.title(f"Dibujo Bot — Tile {tile_num}/{total_tiles}")
    root.attributes('-topmost', True)
    root.attributes('-alpha', 0.6)

    ancho_pantalla = root.winfo_screenwidth()
    alto_pantalla = root.winfo_screenheight()
    root.attributes('-fullscreen', True)

    canvas = tk.Canvas(root, width=ancho_pantalla, height=alto_pantalla, bg='white', highlightthickness=0)
    canvas.pack()

    root.start_x = 0
    root.start_y = 0

    # Calcular centro usando TODOS los contornos para mantener la misma referencia
    cx_img, cy_img = _calcular_centro(todos_contornos)

    # Info de tiles para colorear
    min_x_b, min_y_b, max_x_b, max_y_b = _calcular_bbox(todos_contornos)
    ancho_img = max_x_b - min_x_b
    alto_img = max_y_b - min_y_b
    ancho_t = ancho_img / COLS_MOSAICO if ancho_img > 0 else 1
    alto_t = alto_img / FILAS_MOSAICO if alto_img > 0 else 1

    def actualizar_canvas():
        canvas.delete("all")

        # Título
        canvas.create_text(ancho_pantalla // 2, 25,
                           text=f"TILE {tile_num}/{total_tiles} — Posiciona el zoom en esta zona y pulsa ENTER",
                           font=("Arial", 16, "bold"), fill="#E91E63")

        n_pts = _contar_puntos(trazos_tile)
        t_est = _formato_tiempo(_estimar_tiempo_dibujo(trazos_tile))
        canvas.create_text(ancho_pantalla // 2, 55,
                           text=f"Trazos: {len(trazos_tile)} ({n_pts} pts) | Estimado: ~{t_est} | Rueda: Zoom | Arrastrar: Mover | ESC: Cancelar",
                           font=("Arial", 12), fill="black")

        # Dibujar TODOS los trazos con diferentes estilos según estado
        for t_num in range(1, total_tiles + 1):
            trazos_de_tile = grupos.get(t_num, [])
            if not trazos_de_tile:
                continue

            if t_num < tile_num:
                # Ya dibujados: gris tenue
                color = "#CCCCCC"
                width = 1
            elif t_num == tile_num:
                # Tile actual: color brillante + grueso
                color = _COLORES_TILE[(t_num - 1) % len(_COLORES_TILE)]
                width = 3
            else:
                # Futuros: gris muy claro
                color = "#E8E8E8"
                width = 1

            for contorno in trazos_de_tile:
                puntos_planos = []
                for punto in contorno:
                    px, py = _transformar_punto(punto[0][0], punto[0][1], cx_img, cy_img)
                    puntos_planos.extend([px, py])
                if len(puntos_planos) >= 4:
                    canvas.create_line(puntos_planos, fill=color, width=width)

        # Punto de inicio del tile actual (punto rojo grande)
        if trazos_tile:
            primer_trazo = trazos_tile[0]
            if len(primer_trazo) > 0:
                p0 = primer_trazo[0][0]
                sx, sy = _transformar_punto(p0[0], p0[1], cx_img, cy_img)
                # Círculo grande rojo con borde
                canvas.create_oval(sx - 8, sy - 8, sx + 8, sy + 8,
                                   fill="red", outline="white", width=2)
                canvas.create_text(sx, sy - 18, text="INICIO",
                                   font=("Arial", 10, "bold"), fill="red")

        # Grid overlay
        if ancho_img > 0 and alto_img > 0:
            filas = FILAS_MOSAICO
            cols = COLS_MOSAICO
            ancho_tile = ancho_img / cols
            alto_tile_g = alto_img / filas

            for c in range(cols + 1):
                px_img = min_x_b + c * ancho_tile
                sx_top, sy_top = _transformar_punto(px_img, min_y_b, cx_img, cy_img)
                sx_bot, sy_bot = _transformar_punto(px_img, max_y_b, cx_img, cy_img)
                canvas.create_line(sx_top, sy_top, sx_bot, sy_bot, fill="white", width=3)
                canvas.create_line(sx_top, sy_top, sx_bot, sy_bot, fill="black", width=1, dash=(6, 4))

            for f in range(filas + 1):
                py_img = min_y_b + f * alto_tile_g
                sx_lft, sy_lft = _transformar_punto(min_x_b, py_img, cx_img, cy_img)
                sx_rgt, sy_rgt = _transformar_punto(max_x_b, py_img, cx_img, cy_img)
                canvas.create_line(sx_lft, sy_lft, sx_rgt, sy_rgt, fill="white", width=3)
                canvas.create_line(sx_lft, sy_lft, sx_rgt, sy_rgt, fill="black", width=1, dash=(6, 4))

            num = 1
            for f in range(filas):
                for c_idx in range(cols):
                    cx_t = min_x_b + (c_idx + 0.5) * ancho_tile
                    cy_t = min_y_b + (f + 0.5) * alto_tile_g
                    sx, sy = _transformar_punto(cx_t, cy_t, cx_img, cy_img)
                    if num < tile_num:
                        # Ya hecho: check verde
                        canvas.create_text(sx, sy, text=f"✓{num}",
                                           font=("Arial", 22, "bold"), fill="#4CAF50")
                    elif num == tile_num:
                        # Actual: número grande con color
                        tile_color = _COLORES_TILE[(num - 1) % len(_COLORES_TILE)]
                        canvas.create_text(sx + 1, sy + 1, text=f"►{num}",
                                           font=("Arial", 28, "bold"), fill="white")
                        canvas.create_text(sx, sy, text=f"►{num}",
                                           font=("Arial", 28, "bold"), fill=tile_color)
                    else:
                        # Futuro: gris
                        canvas.create_text(sx, sy, text=str(num),
                                           font=("Arial", 20), fill="#AAAAAA")
                    num += 1

    def hacer_zoom(event):
        global escala
        if hasattr(event, 'delta') and event.delta > 0:
            escala += PASO_ESCALA
        elif hasattr(event, 'num') and event.num == 4:
            escala += PASO_ESCALA
        else:
            escala = max(0.02, escala - PASO_ESCALA)
        escala = round(escala, 2)
        actualizar_canvas()

    def iniciar_arrastre(event):
        root.start_x = event.x
        root.start_y = event.y

    def arrastrar(event):
        global offset_x, offset_y
        dx = event.x - root.start_x
        dy = event.y - root.start_y
        offset_x += dx
        offset_y += dy
        root.start_x = event.x
        root.start_y = event.y
        actualizar_canvas()

    def aceptar(event):
        resultado['iniciar'] = True
        root.quit()
        root.destroy()

    def cancelar(event):
        resultado['iniciar'] = False
        root.quit()
        root.destroy()

    root.bind("<MouseWheel>", hacer_zoom)
    root.bind("<Button-4>", hacer_zoom)
    root.bind("<Button-5>", hacer_zoom)
    root.bind("<ButtonPress-1>", iniciar_arrastre)
    root.bind("<B1-Motion>", arrastrar)
    root.bind("<Return>", aceptar)
    root.bind("<Escape>", cancelar)

    actualizar_canvas()
    root.mainloop()

    return resultado

# ==========================================
# --- VISTA PREVIA EN PAUSA ---
# ==========================================
def mostrar_preview_pausa(contornos_restantes, contornos_hechos, centro_ref):
    """Muestra preview con trazos ya hechos (gris) y restantes (azul).
    Permite reposicionar con rueda/arrastre. Retorna True para continuar, False para cancelar."""
    global escala, rotacion, offset_x, offset_y

    resultado = {'continuar': True}

    root = tk.Tk()
    root.title("Vista previa \u2014 Pausa")
    root.attributes('-topmost', True)
    root.attributes('-alpha', 0.7)

    ancho_pantalla = root.winfo_screenwidth()
    alto_pantalla = root.winfo_screenheight()
    root.attributes('-fullscreen', True)

    canvas = tk.Canvas(root, width=ancho_pantalla, height=alto_pantalla,
                       bg='white', highlightthickness=0)
    canvas.pack()

    cx_img, cy_img = centro_ref
    root.start_x = 0
    root.start_y = 0

    def actualizar_canvas():
        canvas.delete("all")

        canvas.create_text(ancho_pantalla // 2, 25,
                           text="VISTA PREVIA (PAUSA) \u2014 Gris: ya dibujado | Azul: restante",
                           font=("Arial", 15, "bold"), fill="#E91E63")

        n_rest = len(contornos_restantes)
        n_pts = _contar_puntos(contornos_restantes)
        t_est = _formato_tiempo(_estimar_tiempo_dibujo(contornos_restantes))
        canvas.create_text(ancho_pantalla // 2, 55,
                           text=f"Restantes: {n_rest} trazos ({n_pts} pts) | ~{t_est} | "
                                "Rueda: Zoom | Arrastrar: Mover | ENTER: Continuar | ESC: Cancelar",
                           font=("Arial", 12), fill="black")

        # Trazos ya dibujados en gris
        for contorno in contornos_hechos:
            puntos_planos = []
            for punto in contorno:
                px, py = _transformar_punto(punto[0][0], punto[0][1], cx_img, cy_img)
                puntos_planos.extend([px, py])
            if len(puntos_planos) >= 4:
                canvas.create_line(puntos_planos, fill="#CCCCCC", width=1)

        # Trazos restantes en azul
        inicio_x, inicio_y = None, None
        for contorno in contornos_restantes:
            puntos_planos = []
            for punto in contorno:
                px, py = _transformar_punto(punto[0][0], punto[0][1], cx_img, cy_img)
                puntos_planos.extend([px, py])
                if inicio_x is None:
                    inicio_x, inicio_y = px, py
            if len(puntos_planos) >= 4:
                canvas.create_line(puntos_planos, fill="#2196F3", width=2)

        # Punto de inicio del siguiente trazo
        if inicio_x is not None:
            canvas.create_oval(inicio_x - 6, inicio_y - 6,
                               inicio_x + 6, inicio_y + 6,
                               fill="red", outline="white", width=2)
            canvas.create_text(inicio_x, inicio_y - 16, text="SIGUIENTE",
                               font=("Arial", 9, "bold"), fill="red")

    def hacer_zoom(event):
        global escala
        if hasattr(event, 'delta') and event.delta > 0:
            escala += PASO_ESCALA
        elif hasattr(event, 'num') and event.num == 4:
            escala += PASO_ESCALA
        else:
            escala = max(0.02, escala - PASO_ESCALA)
        escala = round(escala, 2)
        actualizar_canvas()

    def iniciar_arrastre(event):
        root.start_x = event.x
        root.start_y = event.y

    def arrastrar(event):
        global offset_x, offset_y
        dx = event.x - root.start_x
        dy = event.y - root.start_y
        offset_x += dx
        offset_y += dy
        root.start_x = event.x
        root.start_y = event.y
        actualizar_canvas()

    def aceptar(event):
        resultado['continuar'] = True
        root.quit()
        root.destroy()

    def cancelar(event):
        resultado['continuar'] = False
        root.quit()
        root.destroy()

    root.bind("<MouseWheel>", hacer_zoom)
    root.bind("<Button-4>", hacer_zoom)
    root.bind("<Button-5>", hacer_zoom)
    root.bind("<ButtonPress-1>", iniciar_arrastre)
    root.bind("<B1-Motion>", arrastrar)
    root.bind("<Return>", aceptar)
    root.bind("<Escape>", cancelar)

    actualizar_canvas()
    root.mainloop()

    return resultado['continuar']


# ==========================================
# --- FUNCIÓN DE DIBUJO (SendInput) ---
# ==========================================
def dibujar_con_mouse(contornos, mostrar_final=True, centro_referencia=None):
    """Dibuja los trazos moviendo el raton. Retorna tiempo total o None si fue abortado.
    centro_referencia: tupla (cx, cy) opcional para usar como centro de transformacion.
                       Si no se pasa, se calcula del propio contorno.
                       IMPORTANTE para tiles: debe coincidir con el centro usado en la preview.
    Controles durante el dibujo:
        ESPACIO = Pausar / Reanudar
        V       = Vista previa (solo en pausa)
        ESC     = Cancelar dibujo"""
    total_puntos = _contar_puntos(contornos)
    t_estimado = _formato_tiempo(_estimar_tiempo_dibujo(contornos))
    print(f"\u00a1Iniciando dibujo! {len(contornos)} trazos, {total_puntos} puntos (estimado: ~{t_estimado})")
    if rotacion != 0:
        print(f"  Rotacion: {rotacion}\u00b0")
    print("  ESPACIO=Pausar | V=Vista previa (en pausa) | ESC=Cancelar")

    t_inicio = time.time()
    trazos_dibujados = 0
    puntos_dibujados = 0
    abortado = False

    # Usar centro externo si se proporciona (tiles), sino calcular del contorno
    if centro_referencia is not None:
        cx_img, cy_img = centro_referencia
    else:
        cx_img, cy_img = _calcular_centro(contornos)

    # Crear overlay de progreso en esquina superior izquierda
    overlay = OverlayDibujo(len(contornos), total_puntos)

    try:
        for i in range(len(contornos)):
            contorno = contornos[i]
            if len(contorno) < 2:
                continue

            # --- Verificar pausa/cancelar entre trazos ---
            overlay.verificar_teclas()
            overlay.actualizar(trazos_dibujados, puntos_dibujados)

            if overlay.cancelado:
                abortado = True
                break

            if overlay.pausado:
                print(f"  \u23f8 Pausa entre trazos ({trazos_dibujados}/{len(contornos)})")
                accion = overlay.esperar_reanudacion(trazos_dibujados, puntos_dibujados)
                if accion == 'cancelar':
                    abortado = True
                    break
                elif accion == 'preview':
                    overlay.cerrar()
                    continuar = mostrar_preview_pausa(
                        contornos[i:], contornos[:i], (cx_img, cy_img))
                    if not continuar:
                        abortado = True
                        break
                    overlay = OverlayDibujo(len(contornos), total_puntos)
                    overlay.pausado = False
                    print(f"  \u25b6 Reanudando desde trazo {i+1}...")
                    time.sleep(0.5)

            # --- Iniciar trazo ---
            primer_punto = contorno[0][0]
            x_ini, y_ini = _transformar_punto(primer_punto[0], primer_punto[1], cx_img, cy_img)

            mover_mouse_abs(x_ini, y_ini)
            time.sleep(0.05)

            mouse_down()
            time.sleep(0.05)

            ultimo_x, ultimo_y = x_ini, y_ini

            for punto in contorno[1:]:
                # Verificar teclas periodicamente
                overlay.verificar_teclas()

                if overlay.cancelado:
                    mouse_up()
                    abortado = True
                    break

                x, y = _transformar_punto(punto[0][0], punto[0][1], cx_img, cy_img)

                mover_mouse_abs(x, y)
                time.sleep(VELOCIDAD_DIBUJADO)

                puntos_dibujados += 1
                ultimo_x, ultimo_y = x, y

                # Actualizar overlay cada 5 puntos (rendimiento)
                if puntos_dibujados % 5 == 0:
                    overlay.actualizar(trazos_dibujados, puntos_dibujados)

                # Verificar desviacion de posicion (movimiento manual)
                cx_cur, cy_cur = obtener_pos_cursor()
                if abs(cx_cur - x) > 30 or abs(cy_cur - y) > 30:
                    mouse_up()
                    overlay.cerrar()
                    t_total = time.time() - t_inicio
                    print(f"\n\u274c Abortado tras {_formato_tiempo(t_total)} ({trazos_dibujados}/{len(contornos)} trazos)")
                    mostrar_alerta_error()
                    return None

                # Manejar pausa dentro de un trazo
                if overlay.pausado:
                    mouse_up()
                    time.sleep(0.05)
                    print(f"  \u23f8 Pausa (durante trazo {i+1})")
                    accion = overlay.esperar_reanudacion(trazos_dibujados, puntos_dibujados)
                    if accion == 'cancelar':
                        abortado = True
                        break
                    elif accion == 'preview':
                        overlay.cerrar()
                        continuar = mostrar_preview_pausa(
                            contornos[i:], contornos[:i], (cx_img, cy_img))
                        if not continuar:
                            abortado = True
                            break
                        overlay = OverlayDibujo(len(contornos), total_puntos)
                        overlay.pausado = False
                        time.sleep(0.5)
                    # Reanudar: reposicionar y volver a pulsar mouse
                    mover_mouse_abs(ultimo_x, ultimo_y)
                    time.sleep(0.05)
                    mouse_down()
                    time.sleep(0.05)

            if abortado:
                break

            mouse_up()
            time.sleep(0.05)
            trazos_dibujados += 1
            overlay.actualizar(trazos_dibujados, puntos_dibujados)

            if trazos_dibujados % 10 == 0:
                t_parcial = time.time() - t_inicio
                pct = trazos_dibujados / len(contornos) * 100
                print(f"  \u23f1 {trazos_dibujados}/{len(contornos)} trazos ({pct:.0f}%) - {_formato_tiempo(t_parcial)} transcurrido")

    finally:
        overlay.cerrar()

    if abortado:
        t_total = time.time() - t_inicio
        print(f"\n\u274c Cancelado tras {_formato_tiempo(t_total)} ({trazos_dibujados}/{len(contornos)} trazos)")
        return None

    t_total = time.time() - t_inicio
    print(f"\u2728 \u00a1Dibujo terminado! {trazos_dibujados} trazos en {_formato_tiempo(t_total)}")
    if mostrar_final:
        mostrar_alerta_terminado(t_total)
    return t_total


def mostrar_alerta_terminado(t_total=0):
    alerta_root = tk.Tk()
    alerta_root.title("Dibujo Bot")
    alerta_root.attributes('-topmost', True)
    alerta_root.withdraw()
    msg = f"El bot ha terminado de dibujar.\nTiempo total: {_formato_tiempo(t_total)}"
    messagebox.showinfo("¡Terminado!", msg)
    alerta_root.destroy()

def mostrar_alerta_error():
    alerta_root = tk.Tk()
    alerta_root.title("Dibujo Bot")
    alerta_root.attributes('-topmost', True)
    alerta_root.withdraw()
    messagebox.showwarning("Cancelado", "El dibujo se detuvo por movimiento manual.")
    alerta_root.destroy()


# ==========================================
# --- PUNTO DE ENTRADA ---
# ==========================================
trazos, t_proc = extraer_coordenadas_negras(RUTA_IMAGEN)

if not trazos:
    print("No se encontraron trazos.")
else:
    print("Abriendo interfaz de ajuste...")
    res = mostrar_interfaz_ajustable(trazos, t_proc, RUTA_IMAGEN)

    if not res['iniciar']:
        print("Operación cancelada por el usuario.")

    elif res['usar_tiles']:
        # ============================
        # MODO TILES (grid activo al pulsar Enter)
        # ============================
        todos_contornos = res['contornos']
        # Agrupar con RECORTE punto a punto (sin contaminación entre tiles)
        grupos = _agrupar_trazos_por_tile(todos_contornos, FILAS_MOSAICO, COLS_MOSAICO)
        total_tiles = FILAS_MOSAICO * COLS_MOSAICO

        # Centro GLOBAL: el mismo que usan la preview principal y mostrar_preview_tile
        centro_global = _calcular_centro(todos_contornos)

        print(f"\n{'='*55}")
        print(f"  DIBUJO POR TILES: {FILAS_MOSAICO}x{COLS_MOSAICO} = {total_tiles} tiles")
        print(f"  Trazos totales: {len(todos_contornos)} ({_contar_puntos(todos_contornos)} pts)")
        print(f"  Centro de referencia: ({centro_global[0]:.1f}, {centro_global[1]:.1f})")
        print(f"{'='*55}")

        tiles_dibujados = 0
        t_total_tiles = 0.0

        for tile_num in range(1, total_tiles + 1):
            trazos_tile = grupos.get(tile_num, [])

            if not trazos_tile:
                print(f"\n  Tile {tile_num}/{total_tiles} — vacío, saltando")
                continue

            n_pts = _contar_puntos(trazos_tile)
            t_est = _formato_tiempo(_estimar_tiempo_dibujo(trazos_tile))

            print(f"\n  Tile {tile_num}/{total_tiles}: {len(trazos_tile)} trazos, {n_pts} pts (~{t_est})")

            # Preview visual: muestra trazos del tile resaltados + grid + punto inicio
            res_tile = mostrar_preview_tile(trazos_tile, tile_num, total_tiles, todos_contornos, grupos)

            if not res_tile['iniciar']:
                print("  Cancelado por el usuario.")
                break

            print(f"  >>> Dibujando tile {tile_num}...")
            time.sleep(1)
            # Pasar centro_global para que coincida con la preview
            t_tile = dibujar_con_mouse(trazos_tile, mostrar_final=False, centro_referencia=centro_global)

            if t_tile is not None:
                t_total_tiles += t_tile
                tiles_dibujados += 1
            else:
                print("  Dibujo abortado.")
                break

        if tiles_dibujados > 0:
            print(f"\n{'='*55}")
            print(f"  TILES COMPLETADOS: {tiles_dibujados}/{total_tiles}")
            print(f"  Tiempo total: {_formato_tiempo(t_total_tiles)}")
            print(f"{'='*55}")
            mostrar_alerta_terminado(t_total_tiles)

    else:
        # ============================
        # MODO NORMAL (sin grid)
        # ============================
        print(">>> Esperando 1s antes de dibujar...")
        time.sleep(1)
        print(">>> ¡Dibujando AHORA!")
        dibujar_con_mouse(res['contornos'])