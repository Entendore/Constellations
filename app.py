#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
ASTERISMA — a field atlas of the night. PySide6 edition.

Run:   pip install PySide6
       python asterisma.py

Everything (stars, tales, planets, saves, sound) lives in this one file.
Saves go to ~/.asterisma.json. QtMultimedia / QtTextToSpeech are optional;
the game runs silently and unspoken if they are absent.
"""
import sys, os, math, json, time, random, array

from PySide6.QtCore import Qt, QTimer, QPointF, QRectF, QUrl, QObject
from PySide6.QtGui import (QPainter, QColor, QPen, QBrush, QRadialGradient, QLinearGradient,
                           QFont, QPixmap, QImage, QAction, QShortcut, QKeySequence,
                           QPainterPath, QGuiApplication)
from PySide6.QtWidgets import (QApplication, QMainWindow, QWidget, QDialog, QLabel, QVBoxLayout,
                               QHBoxLayout, QPushButton, QScrollArea, QFrame, QLineEdit,
                               QListWidget, QListWidgetItem, QTextBrowser, QToolBar, QStatusBar,
                               QDockWidget, QFileDialog, QSizePolicy, QToolButton)

# ============================== helpers ==============================
DEG = math.pi / 180.0
def clamp(v, a, b): return a if v < a else (b if v > b else v)
def rev(x): return ((x % 360.0) + 360.0) % 360.0
def mod24(h): return ((h % 24.0) + 24.0) % 24.0
def deltaH(a, b):
    d = (a - b) % 24.0
    if d > 12: d -= 24
    if d < -12: d += 24
    return d
def ekey(a, b): return a + '|' + b if a < b else b + '|' + a
def hexRGB(h): return int(h[1:3], 16), int(h[3:5], 16), int(h[5:7], 16)
def rom(n): return ['','I','II','III','IV','V','VI','VII','VIII','IX','X','XI','XII'][n] if n < len(['','I','II','III','IV','V','VI','VII','VIII','IX','X','XI','XII']) else str(n)
NUMWORD = ['zero','one','two','three','four','five','six','seven','eight','nine','ten','eleven','twelve']
def angSep(a, b):
    d1, d2, dr = a['dec']*DEG, b['dec']*DEG, (a['ra']-b['ra'])*15*DEG
    return math.acos(clamp(math.sin(d1)*math.sin(d2)+math.cos(d1)*math.cos(d2)*math.cos(dr), -1, 1))/DEG
def easeIO(t): return 4*t*t*t if t < .5 else 1 - math.pow(-2*t+2, 3)/2
def cardinal(az):
    dirs = ['N','NNE','NE','ENE','E','ESE','SE','SSE','S','SSW','SW','WSW','W','WNW','NW','NNW']
    return dirs[int(round(rev(az)/22.5)) % 16]
def fmtRA(h):
    h = mod24(h); hh = int(h); mm = int((h-hh)*60)
    return '%02dʰ%02dᵐ' % (hh, mm)
def fmtDec(d):
    s = '−' if d < 0 else '+'; d = abs(d); dd = int(d); mm = int((d-dd)*60)
    return '%s%02d°%02d′' % (s, dd, mm)
def fmtT(s):
    m = int(s//60); ss = int(round(s % 60)); return '%d:%02d' % (m, ss)
def fmtH(h):
    h = max(0.0, h); hh = int(h); mm = int(round((h-hh)*60))
    if mm == 60: hh += 1; mm = 0
    return '%dʰ%02dᵐ' % (hh, mm)

def _imul(a, b): return (a * b) & 0xFFFFFFFF
def mulberry32(seed):
    s = seed & 0xFFFFFFFF
    def r():
        nonlocal s
        s = (s + 0x6D2B79F5) & 0xFFFFFFFF
        t = s ^ (s >> 15)
        t = (t * ((1 | s) & 0xFFFFFFFF)) & 0xFFFFFFFF
        u = _imul(t ^ (t >> 7), 61 | t) & 0xFFFFFFFF
        t = ((t + u) ^ t) & 0xFFFFFFFF
        t = (t ^ (t >> 14)) & 0xFFFFFFFF
        return t / 4294967296.0
    return r
def gauss_of(rng):
    u = v = 0.0
    while u == 0: u = rng()
    while v == 0: v = rng()
    return math.sqrt(-2*math.log(u))*math.cos(2*math.pi*v)
def qbez(P, t):
    u = 1-t
    return (u*u*P[0][0]+2*u*t*P[1][0]+t*t*P[2][0], u*u*P[0][1]+2*u*t*P[1][1]+t*t*P[2][1])

# ============================== star catalogue (J2000) ==============================
SPEC = {'O':'#a3bcff','B':'#bccfff','A':'#dbe6ff','F':'#f2f4ff','G':'#fff2d4','K':'#ffd9a0','M':'#ffa96e'}
def S(*a):
    d = dict(zip(('id','name','bayer','ra','dec','mag','cls','spec','dist'), a[:9]))
    d['figure'] = a[9] if len(a) > 9 else False
    d['info'] = a[10] if len(a) > 10 else None
    return d
def L(**k):
    k.setdefault('neb', []); k.setdefault('fuzzy', []); k.setdefault('mw', None)
    k.setdefault('viewMin', 0.45); k.setdefault('deep', 0)
    return k

LEVELS = [
L(id='cygnus', name='Cygnus', common='the Swan', center=(20.10, 32.5), view=48, seed=11, embers=4,
  frm='Greece · China · the sky-readers of Australia',
  mw={'pts':[(19.5,20),(20.6,42),(21.6,56)],'width':.34,'glow':1.0,'rift':True},
  neb=[{'ra':20.62,'dec':40.3,'r':1.9,'col':'210,220,250','a':.09}],
  fuzzy=[{'name':'NGC 7000 — the North America Nebula','ra':20.97,'dec':44.33,
          'info':'A vast sheet of glowing hydrogen near Deneb, found by William Herschel in 1786. Almost invisible to the eye; glorious on film and sensor.'}],
  stars=[S('deneb','Deneb','α Cygni',20.6905,45.280,1.25,'A','A2 Ia','≈ 2,600 ly',True),
         S('sadr','Sadr','γ Cygni',20.3712,40.257,2.23,'F','F8 Ib','≈ 1,800 ly',True),
         S('albireo','Albireo','β Cygni',19.5120,27.960,3.05,'K','K3 II + B8','≈ 430 ly',True),
         S('gienah','Aljanah (Gienah)','ε Cygni',20.7702,33.970,2.48,'K','K0 III','≈ 73 ly',True),
         S('fawaris','Fawaris','δ Cygni',19.7494,45.131,2.87,'B','B9 III','≈ 165 ly',True),
         S('vega','Vega','α Lyrae',18.6156,38.784,0.03,'A','A0 V','25 ly'),
         S('altair','Altair','α Aquilae',19.8464,8.868,0.76,'A','A7 V','17 ly'),
         S('zcyg','Zeta Cygni','ζ Cygni',21.2164,30.227,3.20,'G','G8 III','≈ 143 ly'),
         S('icyg','Iota Cygni','ι Cygni',19.4960,51.730,3.79,'A','A5 V','≈ 121 ly'),
         S('kcyg','Kappa Cygni','κ Cygni',19.2878,53.619,3.77,'G','G9 III','≈ 124 ly'),
         S('ecyg','Eta Cygni','η Cygni',19.9340,35.083,3.89,'K','K0 III','≈ 139 ly'),
         S('o1cyg','Omicron¹ Cygni','ο¹ Cygni',20.1170,46.773,3.80,'K','K2 II','≈ 920 ly'),
         S('tcyg','Tau Cygni','τ Cygni',21.2318,37.842,3.72,'F','F2 IV','≈ 69 ly')],
  edges=[('deneb','sadr'),('sadr','albireo'),('sadr','gienah'),('sadr','fawaris')],
  tale="""A swan flies down the Silver River.

The Greeks told of Cycnus, a king who could not stop grieving: when his friend Phaethon fell from the sun's chariot into the river, Cycnus dove again and again to bring him home, until the gods, moved and weary, changed him into the bird he imitated.

In China this stretch of sky is the middle of a love story: two lovers set on opposite banks of the Celestial River, allowed to cross once a year when ten thousand magpies offer themselves as a bridge.

And in Australia, look again: the shape here is drawn not in stars, but in the dark.""",
  notes=['Four lines bind the figure: a long neck down the River, and two wings spread from a single heart.',
         'The heart of the Cross sits in the brightest dust of the Milky Way. The tail is a blue-white supergiant — one of the most powerful stars known.',
         'Stars of the figure breathe with faint ember-light. Draw from ember to ember.',
         'Faint pulses haunt this plate — a nebula shaped like a continent, near the tail. Hover them.'],
  facts=['Deneb, the tail, sits some 2,600 light-years away yet still shines at magnitude 1.3 — it may radiate 200,000 times the light of the Sun. At Vega’s distance it would outshine Venus and cast shadows at night.',
         'Albireo, the beak, is the sky’s most celebrated colour double: a golden giant with a small blue companion beside it — one amber, one sapphire — split even by small telescopes.',
         {'t':'Cygnus X-1, near the neck, was the first object widely accepted to be a black hole. Stephen Hawking bet against it; in 1990 he conceded, and paid up.','at':(20.62,35.2,22)},
         'The Milky Way here is split by the Great Rift — a lane of cold dust hanging between us and the galaxy’s far bank.'],
  cultures=[('Greece','The Mourning King','Cycnus, king of the Ligurians, was the devoted friend of Phaethon. When the sun-chariot failed and Phaethon fell into the river Eridanus, Cycnus dove without end to gather his bones. The gods changed him into a swan — the bird that grieves in silence — and set him upon a river of stars.'),
            ('China','The Magpie Bridge','The Weaver Girl and the Cowherd married, and were punished with separation: the Milky Way set between them. Once a year, on the seventh night of the seventh moon, magpies spread themselves into a bridge so the two may meet. Deneb hangs above the crossing like a lantern; the summer festival of Qixi keeps the date.'),
            ('Australia','The Emu in the Sky','Many Aboriginal nations read a great emu in the Milky Way’s dark lanes — a figure drawn in darkness, its head the Coalsack beside the Southern Cross, its body stretched along the rift past Cygnus. Its tilt through the year told communities when emu eggs were fat: a calendar written in shadow.')]),
L(id='lyra', name='Lyra', common='the Lyre', center=(18.78, 36.2), view=15, seed=71, embers=3, viewMin=0.35,
  frm='Greece · China · the astronomers of Arabia',
  mw={'pts':[(17.6,44),(19.0,31),(20.4,14)],'width':.26,'glow':.55,'rift':False},
  fuzzy=[{'name':'M57 — the Ring Nebula','ra':18.8933,'dec':33.029,
          'info':'A dying sun-like star shedding its glowing shell of gas, 2,300 light-years off. Small telescopes show it as a little smoke-ring between the lyre’s lower stars.'}],
  stars=[S('vega','Vega','α Lyrae',18.6156,38.784,0.03,'A','A0 V','25 ly',True,
           'The fifth-brightest star in the sky, the first star ever photographed (1850) — and the northern pole star twelve thousand years ago.'),
         S('epslyr','ε Lyrae — the Double-Double','ε Lyrae',18.7419,39.670,4.59,'A','A4 V + A','≈ 160 ly',False,
           'Two binary pairs locked in a slow orbit around each other: keen eyes split it into two stars, a small telescope into four.'),
         S('zeta1','Zeta¹ Lyrae','ζ¹ Lyrae',18.7462,37.605,4.36,'A','A4 m','≈ 156 ly',True),
         S('sheliak','Sheliak','β Lyrae',18.8346,33.363,3.52,'B','B7 IIe','≈ 960 ly',True,
           'Two stars so close they trade gas through a bridge; their light dips every 12.9 days as one crosses in front of the other.'),
         S('sulafat','Sulafat','γ Lyrae',18.9826,32.690,3.25,'B','B9 III','≈ 620 ly',True),
         S('delta2','Delta² Lyrae','δ² Lyrae',18.9084,36.899,4.30,'M','M4 III','≈ 740 ly',True),
         S('etal','Eta Lyrae','η Lyrae',19.2321,39.087,4.38,'B','B2.5 IV','≈ 1,000 ly'),
         S('thetal','Theta Lyrae','θ Lyrae',18.5907,32.135,4.36,'K','K0 III','≈ 970 ly')],
  edges=[('vega','zeta1'),('zeta1','sheliak'),('sheliak','sulafat'),('sulafat','delta2'),('delta2','zeta1')],
  tale="""The lyre of Orpheus, hung in the sky.

No player ever matched Orpheus, son of the Muse Calliope: at his music, rivers paused and stones drew near. When his bride Eurydice died, he went down after her, and sang so sadly that the lords of the dead wept — and let her follow him back, on one condition he could not keep.

China knows this corner of the sky differently: here, on the near bank of the Celestial River, sits Zhinü the Weaver Girl herself, waiting for the bridge of magpies that lets her cross to her love once a year.

Arab astronomers named Vega the Swooping Eagle — its partner-name belongs to Altair, the Flying Eagle, on the river's far shore. Two eagles, forever diving at the same stream.""",
  notes=['Five lines: Vega, the bright knot of the strings, tied to a small parallelogram of four.',
         'Between the two lower stars hangs a faint smoke-ring — the ghost of a dying star. Hover it.',
         'One corner of the parallelogram burns deep red: an ancient giant among hot young stars.',
         'Zoom in toward Vega and look just north: a famous “double-double” hides there.'],
  facts=['Vega was the northern pole star around 12,000 BCE and will be again near 13,700 CE: the Earth’s axis wobbles like a spinning top over 25,800 years, so “north” migrates among the stars.',
         'Vega was the first star ever photographed (Harvard, 1850) and the first to have its light spread into a spectrum. For decades astronomers measured all brightness against Vega — magnitude zero, by definition.',
         {'t':'The Ring Nebula is the Sun’s future in miniature: in about five billion years our own star will swell, then drift its outer layers into a glowing ring around a white-hot cinder.','at':(18.8933,33.029,5)},
         'Sheliak is an eclipsing binary — two stars whirling so close that gas flows between them; every 12.9 days one blots the other and the lyre briefly dims.'],
  cultures=[('Greece','Orpheus Down Below','Orpheus charmed the lords of death themselves, but looked back at the edge of daylight and lost Eurydice a second time. When his own end came, Zeus took the lyre and hung it in the heavens — the only instrument allowed to keep playing after the player was gone.'),
            ('China','The Weaver Girl','Zhinü, daughter of the Celestial Emperor, wove the clouds on her loom — the star Vega. Across the River of Heaven, the Cowherd waits with their two children (the stars β and γ Aquilae). Once a year the magpies bridge the dark, and the Weaver crosses to her family.'),
            ('Arabia','The Two Eagles','Arab sky-watchers paired the bright stars of summer: Vega was al-Nasr al-Wāqiʿ, the Swooping Eagle; Altair, across the Milky Way, al-Nasr al-Ṭāʾir, the Flying Eagle. The names flew with the star books into Europe — Vega is simply a Latin misreading of the Arabic.')]),
L(id='crux', name='Crux', common='the Southern Cross', center=(13.35,-59.4), view=26, seed=83, embers=3,
  frm='Aotearoa · Aboriginal Australia · the nations of the southern sea',
  mw={'pts':[(11.6,-64),(13.0,-57),(14.6,-51)],'width':.42,'glow':1.0,'rift':True},
  fuzzy=[{'name':'The Jewel Box (NGC 4755)','ra':12.5367,'dec':-60.345,'blob':(.45,'235,238,255',0.20),
          'info':'A cluster of about a hundred young stars — several among the bluest known — 6,400 light-years off. John Herschel called it the Jewel Box.'},
         {'name':'The Coalsack','ra':12.90,'dec':-62.6,
          'info':'A great cloud of cold dust blotted against the Milky Way, some 600 light-years off — the head of the Emu in many Aboriginal traditions. Not a hole in the stars: a shadow.'}],
  stars=[S('acrupix','Acrux','α Crucis',12.4433,-63.099,0.76,'B','B0.5 IV','≈ 320 ly',True),
         S('mimosa','Mimosa','β Crucis',12.7953,-59.689,1.25,'B','B0.5 III','≈ 280 ly',True),
         S('gacrux','Gacrux','γ Crucis',12.5194,-57.113,1.64,'M','M3.5 III','≈ 89 ly',True),
         S('imai','Imai','δ Crucis',12.2524,-58.749,2.79,'B','B2 IV','≈ 345 ly',True),
         S('rigilkent','Rigil Kentaurus','α Centauri',14.6601,-60.834,-0.27,'G','G2 V + K1 V','4.37 ly',False,
           'The nearest star system to the Sun — two suns so close they look like one star to the eye. A Voyager-speed spacecraft would need roughly 80,000 years for the crossing.'),
         S('hadar','Hadar','β Centauri',14.0638,-60.373,0.61,'B','B1 III','≈ 390 ly',False,
           'The brighter of the two Pointers — though it lies nearly a hundred times farther than its partner. Brightness is no measure of nearness.'),
         S('epscru','ε Crucis','ε Crucis',12.3564,-60.401,3.59,'K','K3 III','≈ 228 ly'),
         S('mucru','μ Crucis','μ Cru',12.6949,-57.183,3.56,'B','B2 V','≈ 370 ly'),
         S('zetacru','ζ Crucis','ζ Cru',12.6919,-55.682,4.04,'B','B2.5 V','≈ 360 ly'),
         S('deltacen','δ Centauri','δ Cen',12.1430,-50.722,2.55,'B','B2 IVne','≈ 380 ly'),
         S('epscen','ε Centauri','ε Cen',13.6647,-53.466,2.30,'B','B1 III','≈ 430 ly')],
  edges=[('acrupix','gacrux'),('mimosa','imai'),('acrupix','mimosa'),('acrupix','imai')],
  tale="""The anchor of the great canoe, hanging low over the southern sea.

To Māori voyagers this was Te Punga — the anchor stone of Te Waka o Rangi, the canoe of the sky. The two brilliant Pointers to the east are the rope, still paid out toward the horizon; the anchor's rise and setting marked the turning of the year.

Along the coasts of Australia, look at the darkness beside the Cross: the Emu of the Milky Way begins here, its head the black cloud the charts call the Coalsack — a figure drawn in shadow, read for thousands of years as a calendar of the seasons.

And there is no bright pole star in the south. The Cross itself serves instead: lean along its long axis, four and a half times, and your finger rests on the empty point around which all this sky turns.""",
  notes=['Four lines: two bright bars crossing in a kite that tapers to Acrux at the foot.',
         'The long bar leans toward two brilliant Pointers to the east — the nearer one is the Sun’s closest neighbour. Hover them.',
         'Beside the Cross the Milky Way carries a dark patch — the Emu’s head. Hover the shadow.',
         'The Cross is a chance gathering: four stars of different ages and distances that will slowly scatter.'],
  facts=['There is no bright south pole star. Navigators extend the Cross’s long axis about 4½ times its length to find the south celestial pole — the southern sky’s compass, trusted across the Pacific for a thousand years of voyaging.',
         {'t':'The four bright stars are not a family: Acrux ~320 ly, Mimosa ~280, Imai ~345 — but Gacrux, the red top, sits only ~89 ly away. They merely pass in line of sight, and will drift apart over millennia.','at':(12.5194,-57.113,9)},
         {'t':'The Pointers are α Centauri — the nearest star system to the Sun at 4.37 light-years — and Hadar, which looks its equal but lies nearly a hundred times farther off.','at':(14.4,-60.7,14)},
         'Five nations carry the Southern Cross on their flags — Australia, Brazil, New Zealand, Papua New Guinea, Samoa. On Brazil’s flag each star stands for a state, and the small fifth star, ε Crucis, was added for one.'],
  cultures=[('Aotearoa','Te Punga, the Anchor','Te Waka o Rangi, the canoe of the sky, rides the heavens with its anchor — Te Punga, the Cross — dropped into the deep, its rope the two Pointers stretching toward the horizon. When the anchor dipped below the evening horizon, the year had turned: time for the plantings and the gatherings.'),
            ('Aboriginal Australia','The Emu’s Head','Beside the Cross, the Coalsack — a dark cloud of cold dust — is the head of the Great Emu stretched along the Milky Way. As the year turns, the Emu’s posture in the sky told communities when the eggs were ready to gather: the calendar was read in the darkness itself.'),
            ('Brazil','The Flag’s Constellation','When Brazil declared its republic in 1889, the new flag placed the stars of that November sky over Rio de Janeiro — the Southern Cross at the centre, one star for each state, the sky made into a map of the nation itself.')]),
L(id='cassiopeia', name='Cassiopeia', common='the Seated Queen', center=(1.03,60.1), view=36, seed=23, embers=4,
  frm='Greece · the Islamic golden age · imperial China',
  mw={'pts':[(22.2,62),(24.6,58.5),(27.2,50)],'width':.3,'glow':.85,'rift':False},
  fuzzy=[{'name':'The Double Cluster','ra':2.345,'dec':57.14,'blob':(.5,'228,234,255',.13),
          'info':'h Persei and χ Persei — two open clusters of hot young stars side by side, some 7,500 light-years away. A naked-eye glow from dark sites.'},
         {'name':'Tycho’s Star (SN 1572)','ra':0.4247,'dec':57.51,
          'info':'Here, on 11 November 1572, Tycho Brahe saw a new star bright enough for daylight — a supernova. His measurements proved the heavens could change.'},
         {'name':'Cassiopeia A','ra':23.392,'dec':58.81,
          'info':'A supernova whose light reached Earth around 1680, seen by almost no one. Today its remnant is the brightest radio source in the sky after the Sun.'}],
  stars=[S('caph','Caph','β Cassiopeiae',0.1529,59.150,2.27,'F','F2 III','≈ 55 ly',True),
         S('schedar','Schedar','α Cassiopeiae',0.6750,56.537,2.24,'K','K0 II–III','≈ 228 ly',True),
         S('navi','Navi (γ Cas)','γ Cassiopeiae',0.9451,60.717,2.47,'B','B0.5 IVe','≈ 550 ly',True),
         S('ruchbah','Ruchbah','δ Cassiopeiae',1.4304,60.235,2.68,'A','A5 III–IV','≈ 99 ly',True),
         S('segin','Segin','ε Cassiopeiae',1.9066,63.670,3.37,'B','B3 III','≈ 410 ly',True),
         S('achird','Achird','η Cassiopeiae',0.8182,57.815,3.44,'F','F9 V + K','≈ 19 ly'),
         S('rhocas','ρ Cassiopeiae','ρ Cas',1.7396,57.498,4.52,'F','F8 Ia hypergiant','≈ 3,400 ly'),
         S('mucas','μ Cassiopeiae','μ Cas',1.1042,54.925,5.17,'G','G1 V','≈ 25 ly')],
  edges=[('caph','schedar'),('schedar','navi'),('navi','ruchbah'),('ruchbah','segin')],
  tale="""A queen in her chair, wheeling forever about the pole.

Cassiopeia boasted herself fairer than the sea-nymphs, and the gods, who punish vanity with an audience, set her throne in the sky where all the world could see — then turned it, night after night, so that half the time she hangs upside down.

A thousand years ago the astronomers of Islam redrew her stars and gave them names we still say: Caph the hand, Schedar the breast, Ruchbah the knee. The sky's vocabulary is largely Arabic, because Islamic astronomy kept and sharpened the Greek maps while Europe slept.

To Chinese observers these five bright stars were Wang Liang, the legendary charioteer, driving the Heavenly Emperor's carriage along the road of stars.""",
  notes=['Five stars, four lines — a letter W painted across the Milky Way itself.',
         'It never sets for most northern lands; its slow wheel around the pole marks the hours.',
         'One of the five spins so fast it nearly tears itself apart — and carries a secret name kept by Apollo’s astronauts.',
         'Three faint pulses haunt this plate — two dead stars and a pair of clusters. Hover them.'],
  facts=['For most northern lands the W never sets. Its slow wheel around the pole — a quarter turn every six hours — makes it a rough clock for anyone who learns to read it.',
         'Gamma Cassiopeiae spins at several hundred kilometres a second, near the tearing point, flinging gas into a glowing disk and flaring without warning. Apollo crews navigated by it under a private name: Navi — Virgil “Gus” Grissom’s middle name, spelled backwards.',
         {'t':'Here on 11 November 1572 Tycho Brahe saw a star bright enough for daylight — a supernova. Its place, far beyond the Moon, showed that the “perfect, unchanging” heavens could change.','at':(0.4247,57.5,12)},
         {'t':'The remnant called Cassiopeia A blew up around 1680, its light reaching an Earth that barely noticed. Today it is the brightest radio source in the sky after the Sun.','at':(23.392,58.8,10)}],
  cultures=[('Greece','The Vanity Sentence','Cassiopeia, queen of Aethiopia, boasted her beauty past the sea-nymphs’. Poseidon sent floods and a sea-monster; her daughter Andromeda was chained as the price, and saved by Perseus. The whole family fills this quarter of the sky — and the queen was strapped to her throne, wheeled about the pole, upside down half the night.'),
            ('The Islamic golden age','The Book of Fixed Stars','In 964 CE the Persian astronomer ʿAbd al-Raḥmān al-Ṣūfī redrew the 48 classical constellations and re-measured their stars. Read the names on this chart — Caph, Schedar, Ruchbah: hand, breast, knee. When European astronomy woke, it woke speaking Arabic.'),
            ('China','Wang Liang Drives','The five bright stars were Wang Liang, master charioteer of the Spring and Autumn period, whipping the Heavenly Emperor’s carriage along Gehu, the sky-road that crosses these stars. A star that flickered was a stumbling horse in the imperial team.')]),
L(id='and', name='Andromeda', common='the Chained Princess', center=(0.85,37.0), view=34, seed=131, embers=4,
  frm='Greece · China · the astronomers of Arabia',
  fuzzy=[{'name':'M31 — the Andromeda Galaxy','ra':0.712,'dec':41.27,'blob':(1.05,'232,238,255',.15),
          'info':'A whole galaxy — a trillion suns — 2.5 million light-years off: the farthest thing most human eyes can see. al-Ṣūfī wrote it down in 964 as “a little cloud”.'},
         {'name':'The open cluster NGC 752','ra':1.944,'dec':37.78,'blob':(.4,'238,238,226',.13),
          'info':'A quiet scattering of about seventy stars a billion years old, far from any dust lane — an ancient, gentle neighbourhood.'}],
  stars=[S('alpheratz','Alpheratz','α Andromedae',0.1398,29.090,2.06,'B','B8 IV + A','≈ 97 ly',True,
           'A shared star: the corner of the Great Square that also belonged to Pegasus — once catalogued as δ Pegasi. One star, two constellations, drawn on the boundary.'),
         S('deltaand','δ Andromedae','δ And',0.6554,30.861,3.27,'K','K3 III','≈ 106 ly',True),
         S('mirach','Mirach','β Andromedae',1.1622,35.621,2.05,'M','M0 III','≈ 197 ly',True,
           'A red giant in the same cool class as Betelgeuse and Antares — with a tiny companion galaxy, NGC 404, hiding just behind it in the glare.'),
         S('almach','Almach','γ Andromedae',2.0650,42.330,2.10,'K','K3 II + B9.5','≈ 350 ly',True,
           'One of the sky’s great colour doubles: a warm gold giant with a blue companion — any small telescope splits it into amber and sapphire.'),
         S('muand','μ Andromedae','μ And',0.9461,38.498,3.87,'A','A5 V','≈ 136 ly',True),
         S('nuand','ν Andromedae','ν And',0.8305,41.076,4.53,'B','B5 V','≈ 620 ly',True),
         S('piand','π Andromedae','π And',0.6153,33.712,4.34,'B','B5 V','≈ 600 ly'),
         S('and51','51 Andromedae','51 And',1.6547,48.630,3.57,'K','K3 III','≈ 180 ly')],
  edges=[('alpheratz','deltaand'),('deltaand','mirach'),('mirach','almach'),('mirach','muand'),('muand','nuand')],
  tale="""The price of a mother's vanity.

Cassiopeia boasted; Poseidon sent the monster; and it was the daughter, Andromeda, chained to the rocks at the sea's edge to appease it. She waits east of her mother's throne still — until Perseus came flying back from slaying Medusa, and made her a princess twice over: once by rescue, once by marriage. The whole quarrelsome family hangs in this quarter of heaven: queen, king, princess, hero, and the beast, forever out of reach of them all.

China drew a different boundary here: these stars are Bì, the Wall — the eastern gate of the Purple Forbidden Enclosure, the walled precinct of the celestial emperor, through which no ordinary star may wander.

And beside the princess's girdle hangs a faint smudge the eye can barely hold. Around 964, the Persian astronomer al-Ṣūfī wrote it down: "a little cloud." It was the Andromeda Galaxy — another island universe, a trillion suns deep, the farthest thing you will ever see without glass.""",
  notes=['Five lines: a chain of stars running from the Great Square of Pegasus — Alpheratz, the shared corner — out through Mirach to Almach, with a small fork to the north.',
         'Beside the chain floats a faint oval patch: another galaxy, naked-eye faint. Hover the pulse.',
         'Almach, the last bright knot, is really two: gold and blue, split by any small telescope.',
         'Zoom to the corner of the Great Square and read the tooltip: one star, two constellations.'],
  facts=[{'t':'M31 is the farthest object most human eyes can see: 2.5 million light-years away. The light arriving tonight left before the genus Homo had quite begun. You are looking at another galaxy with the naked eye — the only one from the northern hemisphere.','at':(0.712,41.27,6)},
         'In the 1970s Vera Rubin and Kent Ford measured how M31 spins: its outer rim moves as fast as its heart, as though unseen mass holds it together. The Andromeda Galaxy is where dark matter stopped being a curiosity and became a problem.',
         'In about four billion years, M31 and the Milky Way will begin to merge — a slow collision over hundreds of millions of years, ending in one larger elliptical galaxy. No stars will collide; the night sky of that far future is beyond guessing.',
         'Alpheratz once carried two names — α Andromedae and δ Pegasi — because it sits on the boundary of both figures. And Almach is one of the finest colour doubles in the sky: gold and blue.'],
  cultures=[('Greece','The Rescued Princess','Andromeda paid for her mother’s tongue: chained to a rock as food for the sea-monster Cetus. Perseus, homeward with the head of Medusa, saw her, fell for her, and turned the beast to stone. The mythographers hung the whole drama in the sky — the chain of stars runs from the Great Square toward her rescuer’s constellation, just above.'),
            ('China','The Wall of the Palace','Alpheratz and its neighbours formed Bì, the Wall — the eastern gate of the Purple Forbidden Enclosure, the celestial emperor’s walled palace-ground around the north pole. It was the most protected real estate in the sky.'),
            ('Arabia','The Little Cloud','In the Book of Fixed Stars, around 964, al-Ṣūfī noted a small nebulous patch near the princess’s mouth — the first written record of the Andromeda Galaxy. European astronomers argued for generations over whether such clouds were nearby fog or far-off universes. They were universes.')]),
L(id='pleiades', name='The Pleiades', common='the Seven Sisters', center=(3.78,24.2), view=6.5, seed=37, embers=5, viewMin=0.16, deep=95,
  frm='Greece · Aotearoa · Japan',
  mw={'pts':[(2.4,44),(3.6,37),(5.5,29)],'width':.3,'glow':.4,'rift':False},
  neb=[{'ra':3.780,'dec':24.11,'r':1.5,'col':'188,208,255','a':.15},
       {'ra':3.772,'dec':23.95,'r':.55,'col':'188,208,255','a':.20},
       {'ra':3.762,'dec':24.34,'r':.5,'col':'188,208,255','a':.11}],
  fuzzy=[{'name':'NGC 1435 — the Merope Nebula','ra':3.772,'dec':23.95,
          'info':'A wisp of dust the cluster is drifting through, lit blue by Merope’s light. In the myth, her veil.'}],
  stars=[S('alcyone','Alcyone','η Tauri',3.7914,24.105,2.87,'B','B7 IIIe','≈ 440 ly',True),
         S('atlas','Atlas','27 Tauri',3.8194,24.053,3.63,'B','B8 III','≈ 440 ly',True),
         S('electra','Electra','17 Tauri',3.7479,24.113,3.70,'B','B6 IIIe','≈ 440 ly',True),
         S('maia','Maia','20 Tauri',3.7636,24.368,3.87,'B','B8 III','≈ 440 ly',True),
         S('merope','Merope','23 Tauri',3.7722,23.948,4.18,'B','B6 IV','≈ 440 ly',True),
         S('taygeta','Taygeta','19 Tauri',3.7543,24.467,4.30,'B','B6 V','≈ 440 ly',True),
         S('pleione','Pleione','28 Tauri',3.8280,24.200,5.09,'B','B8 IVe','≈ 440 ly',True),
         S('celaeno','Celaeno','16 Tauri',3.7495,24.260,5.45,'B','B7 V','≈ 440 ly'),
         S('asterope','Asterope','21 Tauri',3.7605,24.363,5.76,'B','B8 V','≈ 440 ly'),
         S('e18tau','18 Tauri','18 Tau',3.7719,24.491,5.64,'B','B8 V','≈ 440 ly')],
  edges=[('atlas','pleione'),('atlas','alcyone'),('alcyone','electra'),('electra','taygeta'),
         ('taygeta','maia'),('maia','alcyone'),('alcyone','merope')],
  tale="""Seven daughters of the Titan Atlas, chased across the heavens by the Hunter. Zeus gave the sisters wings, then a place in the sky — and set Orion behind them, where he follows to this night and never catches them.

In Aotearoa the cluster is Matariki: when it rises before the winter dawn, the Māori new year begins. The cluster is a mother with her daughters, each charged with a share of the world — food of the soil, food of the trees, fresh water, the sea, the rain, the winds — and the year to come is read in how clearly each one shines.

In Japan they are Subaru, "gathered together" — six stars on a car's badge, one sister out of the picture, as the old count goes.""",
  notes=['Seven stars, seven lines — a small crooked ladle. The sky has been brought close, as through a spyglass.',
         'Other faint sisters drift here: Celaeno and Asterope are true members of the cluster, but the figure wants only the seven bright ones.',
         'One sister is dimmer than her story: they said Merope hid her light for love of a mortal.',
         'A blue wisp hangs near Merope — a veil of dust the cluster is drifting through. Hover the pulse.'],
  facts=['This is not a constellation but a cluster: over a thousand stars born from one cloud about 100 million years ago, still travelling as a family some 440 light-years away.',
         'The blue haze around the sisters is not their own: the cluster is drifting through a dust cloud, and its hot young stars light the dust in reflection.',
         'The Nebra Sky Disc, buried in Germany some 3,600 years ago, may hold the oldest picture of the Pleiades we have. Their dawn risings have marked planting and sailing seasons for at least that long.',
         {'t':'Count them without help: most eyes find six, sharp eyes seven or more. The gap between six and seven was an ancient test of sight — and the ancient answer was story: the lost Pleiad. Celaeno and Asterope wait here, faint.','at':(3.7495,24.26,3)}],
  cultures=[('Greece','The Seven Daughters','Atlas and Pleione had seven daughters. Orion the hunter pursued them — the myth says for seven years — until Zeus turned them into doves, then stars, and set Orion behind them where he still follows. Merope shines faintest: ashamed, the story goes, for loving a mortal.'),
            ('Aotearoa','Matariki','The pre-dawn rising of Matariki in mid-winter opens the Māori new year: a time to name the dead, to plan the plantings, to gather. Each star is a daughter with a charge — soil, forest, fresh water, sea, rain, wind — and the year’s harvest is divined in how clearly each shines. Since 2022, Matariki is an official holiday of Aotearoa New Zealand.'),
            ('Japan','Subaru','Old Japanese skies counted six stars and called the cluster Subaru — “gathered together”. The car maker’s badge shows six, one held back, in the old habit of seeing six where the Greeks counted seven.')]),
L(id='uma', name='Ursa Major', common='the Great Bear', center=(12.30,55.5), view=40, seed=41, embers=5,
  frm='Greece · China · Arabia · North America',
  stars=[S('alkaid','Alkaid','η Ursae Majoris',13.7923,49.313,1.86,'B','B3 V','≈ 104 ly',True),
         S('mizar','Mizar','ζ Ursae Majoris',13.3988,54.925,2.23,'A','A2 V','≈ 83 ly',True,
           'The first double star found in a telescope (1650) — really four suns in two pairs. Alcor beside it was the old test of keen eyesight.'),
         S('alioth','Alioth','ε Ursae Majoris',12.9004,55.960,1.77,'A','A1 III–IVp','≈ 81 ly',True),
         S('megrez','Megrez','δ Ursae Majoris',12.2571,57.033,3.31,'A','A3 V','≈ 81 ly',True),
         S('phecda','Phecda','γ Ursae Majoris',11.8972,53.695,2.44,'A','A0 V','≈ 83 ly',True),
         S('merak','Merak','β Ursae Majoris',11.0307,56.382,2.37,'A','A1 V','≈ 80 ly',True),
         S('dubhe','Dubhe','α Ursae Majoris',11.0621,61.751,1.79,'K','K0 III','≈ 123 ly',True),
         S('alcor','Alcor','80 Ursae Majoris',13.4520,55.420,3.99,'A','A5 V','≈ 86 ly'),
         S('taniaa','Tania Australis','μ Ursae Majoris',10.3722,41.499,3.06,'M','M0 III','≈ 230 ly'),
         S('taniab','Tania Borealis','λ Ursae Majoris',10.2829,42.914,3.45,'A','A2 V','≈ 138 ly'),
         S('thuma','θ Ursae Majoris','θ UMa',11.0972,51.677,3.17,'F','F6 IV','≈ 44 ly'),
         S('psima','ψ Ursae Majoris','ψ UMa',11.1611,44.499,3.00,'K','K1 III','≈ 147 ly'),
         S('chima','χ Ursae Majoris','χ UMa',11.7668,47.779,3.69,'K','K0 III','≈ 196 ly'),
         S('n23','23 Ursae Majoris','23 UMa',10.9688,63.070,3.65,'F','F0 IV','≈ 78 ly')],
  edges=[('merak','dubhe'),('dubhe','megrez'),('megrez','phecda'),('phecda','merak'),
         ('megrez','alioth'),('alioth','mizar'),('mizar','alkaid')],
  tale="""Zeus loved the nymph Callisto; jealousy changed her into a bear, and years later her own son nearly killed her in the hunt. Zeus caught them both up into the sky — the Great Bear and the Little — and Hera, not done, asked that the two never rest or bathe in the ocean's stream: so they wheel about the pole and never set.

Chinese astronomers saw no bear but Bei Dou, the Northern Dipper — the chariot of the celestial court, whose handle marks the seasons: point it east and it is spring under heaven.

Arab sky-watchers saw a funeral: a bier borne by mourning daughters, with Alkaid, "chief of the mourners", at the handle's end.

And in North America, a song told those escaping slavery to follow the Drinking Gourd — the Dipper's pointers — north, to freedom.""",
  notes=['Seven stars, seven lines: a bowl and a bent handle. Begin anywhere; the shape will tell you the rest.',
         'The two stars of the bowl farthest from the handle aim, like an arrow, at the pole star.',
         'One of the seven burns orange — an old red giant among a family of hot white stars.',
         'Beside the handle’s bend a small star hides: Alcor, the old eyesight test, drawn a little wide of Mizar so your eye may share it.'],
  facts=['The Dipper is an asterism — a signpost, not a constellation. The full Bear is the third-largest figure in the sky.',
         {'t':'The two bowl stars farthest from the handle, Merak and Dubhe, point almost exactly to Polaris: extend their line five times and you have true north. In the United States this was sung as “Follow the Drinking Gourd”, a map for escape.','at':(11.05,59,28)},
         'Five of the seven drift through the galaxy together, a family in motion. In 100,000 years the handle will have visibly bent — the Dipper is a temporary drawing.',
         {'t':'Mizar, at the handle’s bend, was the first star found to be double in a telescope (1650). It is really four suns; Alcor beside it is a famous test of keen eyes — and has a small companion of its own.','at':(13.4,55.1,7)}],
  cultures=[('Greece','The Bear Who Never Rests','Callisto, a companion of Artemis, drew the jealousy of Hera and was turned into a bear. Years later her son Arcas met her in the forest and raised his spear. Zeus lifted them both beyond his reach — the Great Bear and the Little — but Hera asked that they never rest: so the bears wheel about the pole, never dipping into the ocean’s stream.'),
            ('China','The Celestial Bureau','Bei Dou, the Northern Dipper, was the chariot of the heavenly emperor, swinging around the pole like the hand of a year-clock: handle east, spring; south, summer; west, autumn; north, winter. Daoist tradition made its stars ministers who hold the registers of life and death.'),
            ('Arabia','The Funeral Bier','Arabic sky-lore saw the bowl as a bier — al-Naʿsh — and the handle as the mourning daughters who follow it, led by Alkaid, “chief of the mourners”. The procession still crosses every northern night, in the names we keep.'),
            ('North America','Follow the Drinking Gourd','A song carried among the enslaved mapped an escape in the sky: keep the Drinking Gourd — the Dipper — high, follow its pointers to Polaris, and walk by night toward free states and Canada. Astronomy at its most consequential.')]),
L(id='orion', name='Orion', common='the Hunter', center=(5.58,0.5), view=40, seed=53, embers=6,
  frm='Greece · ancient Egypt · China',
  mw={'pts':[(4.9,34),(5.8,24),(7.1,-13)],'width':.24,'glow':.3,'rift':False},
  neb=[{'ra':5.588,'dec':-5.45,'r':1.1,'col':'176,224,208','a':.14},
       {'ra':5.68,'dec':-2.3,'r':1.7,'col':'216,120,92','a':.09}],
  fuzzy=[{'name':'The Orion Nebula (M42)','ra':5.588,'dec':-5.39,
          'info':'A stellar nursery some 1,344 light-years away: thousands of infant stars condensing from glowing gas. To the eye it is the faint middle “star” of the sword.'},
         {'name':'The Horsehead Nebula (B33)','ra':5.683,'dec':-2.46,
          'info':'A silhouette of dense dust against red hydrogen glow, just south of Alnitak. Invisible without dark skies and long exposure.'}],
  stars=[S('betelgeuse','Betelgeuse','α Orionis',5.9195,7.407,0.50,'M','M1–2 Ia','≈ 550 ly',True),
         S('bellatrix','Bellatrix','γ Orionis',5.4189,6.350,1.64,'B','B2 III','≈ 250 ly',True),
         S('meissa','Meissa','λ Orionis',5.5864,9.934,3.39,'O','O8 III','≈ 1,100 ly',True),
         S('alnitak','Alnitak','ζ Orionis',5.6793,-1.943,1.77,'O','O9.5 Ib','≈ 1,260 ly',True),
         S('alnilam','Alnilam','ε Orionis',5.6036,-1.202,1.69,'B','B0 Ia','≈ 2,000 ly',True),
         S('mintaka','Mintaka','δ Orionis',5.5334,-0.299,2.23,'O','O9.5 II + B','≈ 1,200 ly',True),
         S('saiph','Saiph','κ Orionis',5.7959,-9.670,2.09,'B','B0.5 Ia','≈ 650 ly',True),
         S('rigel','Rigel','β Orionis',5.2422,-8.202,0.13,'B','B8 Ia','≈ 860 ly',True),
         S('sirius','Sirius','α Canis Majoris',6.7525,-16.716,-1.46,'A','A1 V','8.6 ly'),
         S('aldebaran','Aldebaran','α Tauri',4.5985,16.509,0.87,'K','K5 III','≈ 65 ly'),
         S('alhena','Alhena','γ Geminorum',6.6285,16.399,1.93,'A','A1 IV','≈ 109 ly'),
         S('pi3','π³ Orionis','π³ Ori',4.8307,6.962,3.19,'F','F6 V','≈ 26 ly'),
         S('etaori','η Orionis','η Ori',5.4076,-2.397,3.36,'B','B1 V','≈ 1,000 ly'),
         S('sigmaori','σ Orionis','σ Ori',5.6353,-2.601,3.79,'O','O9.5 V','≈ 1,200 ly'),
         S('hatsya','Hatsya','ι Orionis',5.5847,-5.911,2.77,'O','O9 III','≈ 1,900 ly'),
         S('tauori','τ Orionis','τ Ori',5.2918,-6.844,3.60,'B','B5 III','≈ 555 ly')],
  edges=[('betelgeuse','bellatrix'),('bellatrix','mintaka'),('mintaka','alnilam'),('alnilam','alnitak'),
         ('alnitak','betelgeuse'),('alnitak','saiph'),('saiph','rigel'),('rigel','mintaka')],
  tale="""A hunter of boundless skill boasted that no beast on earth could stand before him. The Earth heard him. A scorpion rose from the soil, and its sting had the last word. The gods set hunter and scorpion at opposite ends of the sky — Orion sets as the Scorpion rises, and the two never share a night.

Egypt knew this figure as Sah, the father of the gods, who strides the sky: the Pyramid Texts say the dead king ascends "as a star within Sah". Stars were not decoration, but destination.

To Chinese astronomers the belt was Shen, "the Three", a mansion of the White Tiger; and on the far side of heaven, in the heart of the Azure Dragon, burned its opposite — the red star called the Great Fire. Poets used the pair for the parted: "In life we do not meet, like Shen and Shang.\"""",
  notes=['Eight lines, an hourglass: two shoulders above, two feet below, and three belt stars between.',
         'The red shoulder and the blue foot are supergiants. Colour is a thermometer — blue burns hotter than red, whatever the size.',
         'Under the belt hangs the sword: its middle “star” is the Orion Nebula, a cloud where stars are being born. A darker shape — the Horsehead — grazes just south of the belt. Hover the faint pulses.',
         'Follow the belt down and left, off this chart, and you would land on Sirius, the brightest star in the sky.'],
  facts=['Two supergiants frame the figure. Betelgeuse, the red shoulder, is cool (≈3,600 K) and so wide it would reach past the orbit of Mars; Rigel, the blue foot, burns at ≈12,000 K with the light of over a hundred thousand Suns. Colour is a thermometer: blue is hotter than red.',
         {'t':'Betelgeuse is near its end. Sometime in the next hundred thousand years it will blaze as a supernova — weeks with the brightness of a half-Moon, visible at noon. In 2019–20 it briefly dimmed, coughing out a dust cloud the whole world watched for.','at':(5.9195,7.407,12)},
         {'t':'The middle “star” of the sword is the Orion Nebula — a nursery 1,344 light-years off where thousands of stars are condensing now, the nearest great star factory.','at':(5.588,-5.39,9)},
         'The Belt lies almost exactly on the celestial equator: it rises within a degree of true east and sets near true west — the sky’s most reliable compass, trusted on every ocean.'],
  cultures=[('Greece','The Boast and the Sting','Orion, son of Poseidon, swore no beast could stand before him. The Earth herself rose against the boast and sent a scorpion from the soil; its sting ended it. Zeus placed the enemies at opposite ends of the sky — the hunter still flees, the scorpion still rises, and the two never share a night.'),
            ('Ancient Egypt','Sah Who Strides','To the builders of the pyramids this was Sah, father of the gods. The Pyramid Texts promise the dead king: “the sky parts for you… you ascend as a star within Sah.” The constellation was not a picture but a destination — the afterlife’s own shore.'),
            ('China','Shen and Shang','The belt was Shen, “the Three”, a mansion of the White Tiger of the West. Directly opposite, in the heart of the Azure Dragon, burned Antares — Shang. The two can never be seen together; Tang poets reached for them whenever fate divided friends: “In life we do not meet — like Shen and Shang.”')]),
L(id='cma', name='Canis Major', common='the Great Dog', center=(6.95,-23), view=30, seed=97, embers=5,
  frm='ancient Egypt · Greece · China',
  mw={'pts':[(5.0,-12),(6.9,-27),(9.3,-44)],'width':.3,'glow':.8,'rift':False},
  fuzzy=[{'name':'M41 — an old, loose cluster','ra':6.783,'dec':-20.74,'blob':(.5,'240,240,226',.15),
          'info':'A scattering of some hundred stars four degrees south of Sirius — possibly the “cloudy one” Aristotle noted around 325 BCE, then forgotten for 1,800 years.'},
         {'name':'NGC 2359 — Thor’s Helmet','ra':7.253,'dec':-13.25,
          'info':'A blue bubble of gas blown by one of the most violent stars known — a Wolf-Rayet wind slamming into space at 1,500 km a second.'}],
  stars=[S('sirius','Sirius','α Canis Majoris',6.7525,-16.716,-1.46,'A','A1 V + white dwarf','8.6 ly',True,
           'The brightest star of the night — a blue-white neighbour at 8.6 light-years. Beside it orbits Sirius B, a white dwarf the size of Earth with the mass of the Sun.'),
         S('mirzam','Mirzam','β Canis Majoris',6.3783,-17.956,1.98,'B','B1 II','≈ 500 ly',True),
         S('wezen','Wezen','δ Canis Majoris',7.1399,-26.393,1.83,'F','F8 Ia','≈ 1,600 ly',True),
         S('adhara','Adhara','ε Canis Majoris',6.9771,-28.972,1.50,'B','B2 II','≈ 430 ly',True),
         S('aludra','Aludra','η Canis Majoris',7.4016,-29.303,2.45,'B','B5 Ia','≈ 2,000 ly',True),
         S('muliphein','Muliphein','γ Canis Majoris',7.0608,-15.633,4.11,'B','B8 II','≈ 440 ly',True),
         S('furud','Furud','ζ Canis Majoris',6.3390,-30.06,3.02,'B','B2.5 V','≈ 336 ly'),
         S('o2cma','ο² Canis Majoris','ο² CMa',7.0308,-23.834,3.02,'B','B3 Ia','≈ 2,600 ly'),
         S('naos','Naos','ζ Puppis',8.0600,-40.003,2.21,'O','O4 If','≈ 1,080 ly')],
  edges=[('sirius','mirzam'),('sirius','muliphein'),('sirius','wezen'),('wezen','adhara'),('wezen','aludra')],
  tale="""The Hunter’s dog, at his heel — the brightest star in all the sky worn as a collar-stone.

Egypt watched this star more closely than any other. They called it Sothis, and when it rose before the dawn out of the summer haze, the Nile was rising too: the flood that made Egypt possible. The new year began with Sirius. A calendar of 365 days was built to meet it — the star kept the time, and the river kept the promise.

Greece told of Laelaps, the hound that always caught what it chased, set upon a fox that could never be caught. The paradox stalled Zeus himself; he turned both to stone — and lifted the hound here, forever mid-chase, forever at the Hunter’s heel.

In China the figure was Tiangou, the celestial dog, whose bite is the eclipse: when the Moon or the Sun darkened, people ran outdoors to bang pots and cymbals until the dog let go.""",
  notes=['Five lines: the bright head near Orion’s feet, a forepaw reaching toward the Hunter, and two hind legs below.',
         'Mirzam means “the announcer” — it rises before Sirius, heralding the Dog Star.',
         'A loose knot of stars hangs just south of the brightest one — a cluster older than the pyramids’ records. Hover the pulse.',
         'A fainter ghost lies to the north-east — a bubble blown by a dying, ferocious star. Hover it.'],
  facts=[{'t':'Sirius is really two stars: Sirius A and Sirius B — the first white dwarf ever found (Alvan Clark, 1862). Sirius B packs the Sun’s mass into an Earth-sized sphere: a teaspoonful of it would weigh tonnes.','at':(6.7525,-16.716,2.4)},
         'Adhara, the hind leg, looks like a modest star beside Sirius — yet it radiates several thousand times the Sun’s light, far outshining Sirius in truth. Sirius only wins because it lives next door. Brightness is an accident of distance.',
         {'t':'M41, south of Sirius, is an open cluster of some hundred stars visible to the naked eye — quite possibly the “cloudy one” Aristotle recorded around 325 BCE.','at':(6.783,-20.74,5)},
         'When Sirius rose with the Sun in July, Greeks and Romans blamed it for the season’s fevers — the “dog days” — a phrase still in every weather report, five millennia on.'],
  cultures=[('Ancient Egypt','Sothis, Lady of the Year','Sothis — Sirius — was the herald of the inundation: its dawn rising out of the summer haze announced that the Nile would soon flood and renew the fields. The Egyptian new year began with the star, and the 365-day calendar was built to keep pace with it. “Sothis rises — the river does too.”'),
            ('Greece','Laelaps, the Inevitable','Laelaps was a hound so swift that nothing escaped it — until Zeus set it upon the Teumessian fox, which no creature could ever catch. Faced with an unstoppable dog chasing an uncatchable fox, Zeus ended the paradox: he turned both to stone, and set the hound in the sky at the Hunter’s heel.'),
            ('China','Tiangou Eats the Moon','The celestial dog Tiangou was blamed when the Sun or Moon went dark: the dog had bitten it. The remedy was noise — drums, gongs, pots banged in the street until the startled dog dropped its meal and light returned. Eclipse lore as community event.')]),
L(id='scorpius', name='Scorpius', common='the Scorpion', center=(16.85,-31.5), view=52, seed=67, embers=8,
  frm='Greece · Polynesia · China',
  mw={'pts':[(14.9,-26),(16.9,-40),(18.3,-23)],'width':.4,'glow':1.0,'rift':False},
  neb=[{'ra':17.9,'dec':-28.5,'r':2.2,'col':'255,214,170','a':.10}],
  fuzzy=[{'name':'The Globular Cluster M4','ra':16.393,'dec':-26.53,'blob':(.9,'235,230,215',.16),
          'info':'One of the nearest globular clusters (~7,200 ly): hundreds of thousands of stars older than the Sun — with Antares blazing in the same eyepiece.'},
         {'name':'Ptolemy’s Cluster (M7)','ra':17.89,'dec':-34.8,'blob':(1.1,'238,238,226',.12),
          'info':'Recorded by Ptolemy in 130 CE — a naked-eye cluster of some eighty young stars rising along the Scorpion’s tail.'}],
  stars=[S('acrab','Acrab','β¹ Scorpii',16.0906,-19.805,2.62,'B','B1 V','≈ 400 ly',True),
         S('dschubba','Dschubba','δ Scorpii',16.0056,-22.622,2.29,'B','B0.3 IV','≈ 400 ly',True),
         S('fang','Fang','π Scorpii',15.9810,-26.114,2.89,'B','B1 V','≈ 460 ly',True),
         S('alniyat','Alniyat','σ Scorpii',16.3531,-25.593,2.89,'B','B1 III','≈ 700 ly',True),
         S('antares','Antares','α Scorpii',16.4901,-26.432,1.06,'M','M1.5 Iab','≈ 550 ly',True),
         S('paikauhale','Paikauhale','τ Scorpii',16.5984,-28.216,2.82,'B','B0.2 V','≈ 470 ly',True),
         S('larawag','Larawag','ε Scorpii',16.8361,-34.293,2.29,'K','K1 III','≈ 64 ly',True),
         S('xamidimura','Xamidimura','μ¹ Scorpii',16.8634,-38.048,3.00,'B','B1.5 V','≈ 500 ly',True),
         S('zeta2','ζ² Scorpii','ζ² Sco',16.9118,-42.361,3.62,'K','K4 III','≈ 132 ly',True),
         S('etasco','η Scorpii','η Sco',17.2025,-43.239,3.33,'F','F3 II–III','≈ 73 ly',True),
         S('sargas','Sargas','θ Scorpii',17.6220,-42.998,1.87,'F','F1 II','≈ 300 ly',True),
         S('iota1','ι¹ Scorpii','ι¹ Sco',17.7933,-40.127,3.03,'F','F2 Ia','≈ 1,930 ly',True),
         S('shaula','Shaula','λ Scorpii',17.5601,-37.104,1.62,'B','B2 IV','≈ 570 ly',True),
         S('lesoath','Lesoath','υ Scorpii',17.4980,-38.100,2.70,'B','B2 IV','≈ 580 ly'),
         S('jabbah','Jabbah','ν Scorpii',16.1949,-31.720,4.00,'B','B2 V','≈ 470 ly'),
         S('rhosco','ρ Scorpii','ρ Sco',15.6654,-29.211,3.87,'B','B2 V','≈ 270 ly'),
         S('omega1','ω¹ Scorpii','ω¹ Sco',16.1229,-37.286,3.95,'B','B1 V','≈ 490 ly'),
         S('kappasco','κ Scorpii','κ Sco',17.7081,-39.030,2.39,'B','B1.5 V','≈ 480 ly'),
         S('zuben','Zubeneschamali','β Librae',15.2829,-9.383,2.61,'B','B8 V','≈ 185 ly')],
  edges=[('fang','dschubba'),('dschubba','acrab'),('dschubba','alniyat'),('alniyat','antares'),
         ('antares','paikauhale'),('paikauhale','larawag'),('larawag','xamidimura'),
         ('xamidimura','zeta2'),('zeta2','etasco'),('etasco','sargas'),('sargas','iota1'),('iota1','shaula')],
  tale="""This is the beast that ended the Hunter — placed, by way of mercy, on the far side of the sky. Its red heart, Antares, is a dying giant so vast that, set where our Sun stands, its surface would swallow the orbit of Mars.

Across Polynesia the curl is not a beast but a tool: the fish-hook of the demigod Māui, with which he hauled great islands up from the sea — the hook itself hangs in the sky above the ocean it made.

China saw the whole figure as the heart of the Azure Dragon of the East. Its red heart-star the classics call the Great Fire: when it sank low in the west, the songs say, the heat of the year was ending, and the harvest was brought in.""",
  notes=['The longest figure in the atlas: thirteen stars, twelve lines — a hooked head, a red heart, and a tail that curls to a point.',
         'Two stars make the sting; the brighter, Shaula, means “the raised tail”.',
         'From northern lands the Scorpion skims the horizon; from the south it stands overhead.',
         'Off to the upper left shines Zubeneschamali — once the Scorpion’s northern claw, until the Romans cut the claws away to make the Scales.',
         'Two round glows of ancient light drift near the tail — clusters of stars older than the Sun. Hover the pulses.'],
  facts=[{'t':'Antares is a red supergiant some 700 times the Sun’s width; set at the Sun’s place, its surface would swallow the orbit of Mars. Its name is Greek — “rival of Ares” — because its red competes with Mars itself when the planet passes near.','at':(16.49,-26.43,7)},
         'Like Betelgeuse, Antares is near death: one day it will flare as a supernova in the daytime sky. Astronomically “one day”; for the star, it is nearly written.',
         'The Sun actually crosses Scorpius in late November. Precession has slid the zodiac about a month against the calendar: the sign of Scorpio and the stars of the Scorpion no longer agree.',
         {'t':'The tail’s stars carry names from everywhere: Shaula and Lesoath from Arabic, Fang from Chinese, Larawag from the Wardaman people of Australia, Paikauhale from Hawaiian. This atlas was written by everyone.','at':(17.89,-34.8,14)}],
  cultures=[('Greece','The Hunter’s End','The scorpion that killed Orion was sent, some say by Artemis, some by the Earth herself. Zeus set it across the sky from its victim — which is why you will search in vain for both at once. The one story of this figure is distance: it exists to be elsewhere.'),
            ('Polynesia','Māui’s Fish-Hook','The demigod Māui cast a magic hook into the deep and hauled up great islands — Te Ika-a-Māui, the fish of Māui, is the North Island of Aotearoa. In many Polynesian traditions the hook hangs in the sky still, curled where the great fish pass beneath it: the Scorpion’s tail.'),
            ('China','The Heart of the Azure Dragon','Antares was Dà Huǒ, “the Great Fire”, heart of the Azure Dragon of the East. The Book of Odes marks the season by it — “the Fire sinks in the west” — the sign that summer’s heat was ending, and the harvest near. It is Shang of the saying “like Shen and Shang”: the star you cannot meet.')]),
L(id='perseus', name='Perseus', common='the Hero', center=(3.45,45.5), view=32, seed=149, embers=6,
  frm='Greece · China · the astronomers of Arabia',
  mw={'pts':[(1.6,58),(3.0,50),(4.6,38)],'width':.3,'glow':.85,'rift':False},
  fuzzy=[{'name':'The Double Cluster','ra':2.345,'dec':57.14,'blob':(.5,'228,234,255',.14),
          'info':'χ and h Persei — two open clusters of hot young stars side by side, 7,500 light-years off, trailing the hero’s sword hand.'},
         {'name':'M34 — a loose cluster','ra':2.712,'dec':42.75,'blob':(.4,'238,238,226',.13),
          'info':'About a hundred stars, 1,500 light-years off, scattered between Algol and γ Andromedae.'},
         {'name':'NGC 1499 — the California Nebula','ra':4.038,'dec':36.6,
          'info':'A vast sheet of glowing hydrogen two and a half Moon-widths long, lit by the O-star ξ Persei — named for its shape on photographs.'}],
  stars=[S('mirfak','Mirfak','α Persei',3.4054,49.861,1.79,'F','F5 Ib','≈ 510 ly',True,
           'The brightest member of the α Persei cluster — a loose family of about a hundred young stars spread across three degrees of sky around it.'),
         S('algol','Algol','β Persei',3.1361,40.956,2.12,'B','B8 V + K eclipsing','≈ 90 ly',True,
           'The “winking demon”: every 2 days 20 hours 49 minutes a companion crosses in front, and the star dims to magnitude 3.4 for ten hours — plain to the naked eye.'),
         S('deltaper','δ Persei','δ Per',3.7153,47.788,3.01,'B','B5 III','≈ 520 ly',True),
         S('gamper','γ Persei','γ Per',3.0796,53.506,2.93,'G','G8 III','≈ 250 ly',True),
         S('etaper','η Persei','η Per',2.8410,55.895,3.76,'K','K3 Iab','≈ 1,300 ly',True),
         S('epsper','ε Persei','ε Per',3.9644,40.010,2.90,'B','B0.5 III','≈ 640 ly',True),
         S('xiper','ξ Persei','ξ Per',3.9585,35.786,4.04,'O','O7.5 III','≈ 1,800 ly',True,
           'One of the very few O-type stars visible without a telescope — the rarest, hottest, shortest-lived class of star, and the light behind the California Nebula.'),
         S('zetaper','ζ Persei','ζ Per',3.9022,31.884,2.85,'B','B1 Ib','≈ 750 ly'),
         S('rhoper','ρ Persei','ρ Per',3.0904,38.840,3.39,'M','M3 II var','≈ 320 ly')],
  edges=[('mirfak','deltaper'),('deltaper','gamper'),('gamper','etaper'),('mirfak','algol'),
         ('deltaper','epsper'),('epsper','xiper'),('xiper','zetaper')],
  tale="""The hero, holding the head of the Gorgon.

Perseus flew home from the killing of Medusa with her head in a bag — and above Andromeda's chains he used it, turning a sea-monster to stone and winning a princess. The Greeks set the whole rescue in this quarter of heaven: the hero stands above the chained princess still, the sword in one hand and the head in the other.

Look to the star the old sky-watchers treated carefully. Algol — the Arabs called it Ra's al-Ghūl, the Head of the Demon — is the Gorgon's eye, and it blinks: every third night, almost to the minute, it dims for ten hours, plainly visible to anyone who cares to watch. Some researchers read a record of exactly that rhythm in an Egyptian calendar papyrus three thousand years old.

China drew no hero here. Around Mirfak lies Tiānchuān, the Celestial Boat, sailing the northern bank of the River of Heaven; around Algol lies Dàlíng, the Great Tomb, with its lines of mourners — and its brightest star marked as the tomb's own eye.

And every August the sky rains. The Perseids — Europe's "tears of Saint Lawrence" — stream from a point beside the hero's sword: dust of comet Swift–Tuttle, meeting the air at fifty-nine kilometres a second.""",
  notes=['Seven lines: a deep arc of three above, a long arm reaching south, and the hand that holds the winking star Algol.',
         'Mirfak anchors a loose cluster of a hundred stars — the field around it is richer than it looks. Hover the pulses.',
         'A naked-eye O-star hides here — the rarest visible class of star. It lights a nebula shaped like a continent.',
         'The Double Cluster spills over this plate’s western edge — two crowds of young suns.'],
  facts=[{'t':'Algol’s eclipse is real and watchable: every 2 days 20 hours 49 minutes a cooler giant passes in front, and the star drops from magnitude 2.1 to 3.4 for about ten hours. A Cairo calendar papyrus may record the period from around 1200 BCE.','at':(3.1361,40.956,8)},
         'ξ Persei is an O-type star — the Galaxy makes them rarely and they die young. Almost all are far beyond the naked eye; this one is an exception, and its ultraviolet light paints the California Nebula.',
         'The Perseids peak every 11–13 August at up to a hundred meteors an hour: grains of comet 109P/Swift–Tuttle striking the air at 59 km/s — among the fastest things that ever glow over your head.',
         {'t':'The Double Cluster, on the border with Cassiopeia, is two crowds of several thousand young stars side by side — a pair of siblings 7,500 light-years off, each only a few million years old.','at':(2.345,57.14,12)}],
  cultures=[('Greece','The Hero and the Gorgon','Perseus, son of Zeus, was sent for the Gorgon Medusa’s head — a gift-job designed to kill him. He returned with it, used it on the sea-monster sent for Andromeda, and married her. The star charts gave the hero the Gorgon’s head itself: Algol, the winking eye in his hand.'),
            ('China','The Tomb and the Boat','Chinese astronomers spread two figures across these stars. Tiānchuān, the Celestial Boat, sailed the northern bank of the River of Heaven around Mirfak. Around Algol lay Dàlíng, the Great Tomb, ringed with nine stars of mourners — and the tomb’s own eye was the star that visibly winked.'),
            ('Arabia','Ra’s al-Ghūl','Arabic sky-lore named the variable star Ra’s al-Ghūl — the Head of the Demon, the winking eye of a ghoul in the tale-cycle of the Gorgon’s head. Translators carried the name into Latin and English whole: every time an astronomer says “Algol”, they speak a sentence of medieval Arabic.')]),
]
for i, lv in enumerate(LEVELS):
    lv['numeral'] = rom(i+1); lv['map'] = {s['id']: s for s in lv['stars']}

MONTHS = ['Jan','Feb','Mar','Apr','May','Jun','Jul','Aug','Sep','Oct','Nov','Dec']
def best_months(lv):
    target = lv['center'][0]*15; out = []; yr = 2024.0
    for m in range(12):
        d = 10957.5 + m*30.4
        g = (280.46061837 + 360.98564736629*d) % 360
        out.append(abs(((g-target) % 360 + 540) % 360 - 180) <= 15)
    return out
def month_label(arr):
    if all(arr): return 'all year'
    if not any(arr): return ''
    best = None
    for s in range(12):
        if not arr[s]: continue
        e = s
        while arr[(e+1) % 12] and (e+1) % 12 != s: e = (e+1) % 12
        ln = ((e-s) % 12) + 1
        if best is None or ln > best[2]: best = (s, e, ln)
    return f'{MONTHS[best[0]]} – {MONTHS[best[1]]}' if best else ''
for lv in LEVELS: lv['months'] = best_months(lv)

OVERTURE = dict(id='overture', seed=99, center=(12,20), view=110, viewMin=0.6, embers=0,
                mw={'pts':[(17.5,-28),(18.6,4),(20.6,42)],'width':.34,'glow':.7,'rift':False},
                neb=[], fuzzy=[], explore=False, tour=False,
                stars=[S('arcturus','Arcturus','α Boötis',14.2610,19.182,-0.05,'K','K1.5 III','37 ly'),
                       S('spica','Spica','α Virginis',13.4199,-11.161,0.97,'B','B1 III','≈ 250 ly'),
                       S('regulus','Regulus','α Leonis',10.1395,11.967,1.35,'B','B8 IV','79 ly'),
                       S('antares','Antares','α Scorpii',16.4901,-26.432,1.06,'M','M1.5 Iab','≈ 550 ly')])

TOUR = dict(id='tour', tour=True, explore=False, center=(12.4,0), view=96, viewMin=0.085, seed=123, embers=0,
            mw={'pts':[(2,58),(13,5),(18.4,-35)],'width':.55,'glow':.8,'rift':True}, neb=[], fuzzy=[], stars=[], edges=[])
_byId = {}
for _l in LEVELS:
    for _s in _l['stars']:
        _o = _byId.get(_s['id'])
        if not _o or (_s['figure'] and not _o['figure']): _byId[_s['id']] = _s
TOUR['stars'] = list(_byId.values())
_seen = set(); TOUR['edges'] = []
for _l in LEVELS:
    for _e in _l['edges']:
        k = ekey(*_e)
        if k not in _seen: _seen.add(k); TOUR['edges'].append(_e)
TOUR['map'] = {s['id']: s for s in TOUR['stars']}

POLE_N = [S('polaris','Polaris','α Ursae Minoris',2.5303,89.264,1.98,'F','F7 Ib','≈ 430 ly',False,
            'The north pole star — less than a degree from the true pole. Not the brightest star, merely the steadiest address.'),
          S('kochab','Kochab','β Ursae Minoris',14.8451,74.155,2.08,'K','K4 III','≈ 130 ly'),
          S('pherkad','Pherkad','γ Ursae Minoris',15.3455,71.834,3.05,'A','A3 II–III','≈ 490 ly'),
          S('yildun','Yildun','δ Ursae Minoris',17.5369,86.586,4.36,'A','A1 V','≈ 170 ly')]
POLE_S = [S('sigmaoct','σ Octantis','σ Octantis',21.1451,-88.957,5.47,'F','F0 III','≈ 270 ly',False,
            'Polaris Australis — the southern pole star: barely fifth magnitude, no guide at all. The south finds its way by the Cross instead.')]

# ============================== the living sky ==============================
ECL = 23.4393*DEG
def ephem_sun(d):
    w = 282.9404+4.70935e-5*d; e = 0.016709-1.151e-9*d; M = rev(356.0470+0.9856002585*d)
    E = M + (180/math.pi)*e*math.sin(M*DEG)*(1+e*math.cos(M*DEG))
    xv = math.cos(E*DEG)-e; yv = math.sqrt(1-e*e)*math.sin(E*DEG)
    v = rev(math.atan2(yv, xv)/DEG); r = math.hypot(xv, yv); lon = rev(v+w)
    x = math.cos(lon*DEG); y = math.sin(lon*DEG)
    return {'lon':lon,'ra':rev(math.atan2(y*math.cos(ECL), x)/DEG),'dec':math.asin(y*math.sin(ECL))/DEG,'dist':r}
def kepler(el, d):
    N = rev(el['N0']+el['Nc']*d); i = el['i0']+el['ic']*d; w = rev(el['w0']+el['wc']*d)
    a = el['a']; e = el['e0']+el['ec']*d; M = rev(el['M0']+el['Mc']*d)
    E = M + (180/math.pi)*e*math.sin(M*DEG)*(1+e*math.cos(M*DEG))
    for _ in range(2): E = M + (180/math.pi)*e*math.sin(E*DEG)*(1+e*math.cos(E*DEG))
    xv = a*(math.cos(E*DEG)-e); yv = a*math.sqrt(1-e*e)*math.sin(E*DEG)
    v = math.atan2(yv, xv); r = math.hypot(xv, yv); u = v+w
    cu, su = math.cos(u), math.sin(u); cN, sN = math.cos(N*DEG), math.sin(N*DEG); ci = math.cos(i*DEG)
    return (r*(cN*cu-sN*su*ci), r*(sN*cu+cN*su*ci), r*su*math.sin(i*DEG))
def to_eq(x, y, z):
    ye = y*math.cos(ECL)-z*math.sin(ECL); ze = y*math.sin(ECL)+z*math.cos(ECL)
    return rev(math.atan2(ye, x)/DEG), math.asin(ze/math.hypot(x, ye, ze))/DEG
PLANETS = [
 {'id':'mercury','name':'Mercury','col':'#c9c4ba','mag':0.0,
  'note':'the smallest planet and the swiftest — it hugs the Sun so tightly that it hides in twilight.',
  'el':{'N0':48.3313,'Nc':3.24587e-5,'i0':7.0047,'ic':5.00e-8,'w0':29.1241,'wc':1.01444e-5,'a':0.387098,'e0':0.205635,'ec':5.59e-10,'M0':168.6562,'Mc':4.0923344368}},
 {'id':'venus','name':'Venus','col':'#f2e8d2','mag':-4.1,
  'note':'the brightest planet — an Earth-sized world wrapped in unbroken cloud, hot enough to melt lead.',
  'el':{'N0':76.6799,'Nc':2.46590e-5,'i0':3.3946,'ic':2.75e-8,'w0':54.8910,'wc':1.38374e-5,'a':0.723330,'e0':0.006773,'ec':-1.302e-9,'M0':48.0052,'Mc':1.6021302244}},
 {'id':'mars','name':'Mars','col':'#e89a6a','mag':0.6,
  'note':'the rusted desert world — its colour is iron-oxide dust, and it brightens hugely every 26 months.',
  'el':{'N0':49.5574,'Nc':2.11081e-5,'i0':1.8497,'ic':-1.78e-8,'w0':286.5016,'wc':2.92961e-5,'a':1.523688,'e0':0.093405,'ec':2.516e-9,'M0':18.6021,'Mc':0.5240207766}},
 {'id':'jupiter','name':'Jupiter','col':'#e9dcc0','mag':-2.4,
  'note':'the giant of the system — heavier than every other planet combined, with four moons visible in binoculars.',
  'el':{'N0':100.4542,'Nc':2.76854e-5,'i0':1.3030,'ic':-1.557e-7,'w0':273.8777,'wc':1.64505e-5,'a':5.20256,'e0':0.048498,'ec':4.469e-9,'M0':19.8950,'Mc':0.0830853001}},
 {'id':'saturn','name':'Saturn','col':'#e6d9a8','mag':0.7,
  'note':'the ringed giant — rings of drifting ice, and a world so light it would float, given an ocean.',
  'el':{'N0':113.6634,'Nc':2.38980e-5,'i0':2.4886,'ic':-1.081e-7,'w0':339.3939,'wc':2.97661e-5,'a':9.55475,'e0':0.055546,'ec':-9.499e-9,'M0':316.9670,'Mc':0.0334442282}}]
def phase_name(age):
    T = [(1.0,'New Moon'),(6.38,'Waxing Crescent'),(8.38,'First Quarter'),(13.77,'Waxing Gibbous'),
         (15.77,'Full Moon'),(21.15,'Waning Gibbous'),(23.15,'Last Quarter'),(28.53,'Waning Crescent'),(29.54,'New Moon')]
    for t, n in T:
        if age < t: return n
    return 'New Moon'
def ephem_moon(d):
    N = rev(125.1228-0.0529538083*d); i = 5.1454; w = rev(318.0634+0.1643573223*d)
    a = 60.2666; e = 0.054900; M = rev(115.3654+13.0649929509*d)
    E = M + (180/math.pi)*e*math.sin(M*DEG)*(1+e*math.cos(M*DEG))
    for _ in range(2): E = M + (180/math.pi)*e*math.sin(E*DEG)*(1+e*math.cos(E*DEG))
    xv = a*(math.cos(E*DEG)-e); yv = a*math.sqrt(1-e*e)*math.sin(E*DEG)
    v = math.atan2(yv, xv); r = math.hypot(xv, yv); u = v+w
    cu, su = math.cos(u), math.sin(u); cN, sN = math.cos(N*DEG), math.sin(N*DEG)
    xe = r*(cN*cu-sN*su*math.cos(i*DEG)); ye = r*(sN*cu+cN*su*math.cos(i*DEG)); ze = r*su*math.sin(i*DEG)
    lon = rev(math.atan2(ye, xe)/DEG); lat = math.atan2(ze, math.hypot(xe, ye))/DEG
    Ms = rev(356.0470+0.9856002585*d); Ls = rev(282.9404+4.70935e-5*d+Ms)
    Lm = rev(N+w+M); D_ = rev(Lm-Ls); F = rev(Lm-N); sn = lambda x: math.sin(x*DEG)
    lon = rev(lon - 1.274*sn(M-2*D_) + 0.658*sn(2*D_) - 0.185*sn(Ms) - 0.059*sn(2*M-2*D_) - 0.057*sn(M-2*D_+Ms) + 0.053*sn(M+2*D_))
    lat += -0.173*sn(F-2*D_) - 0.055*sn(M-F-2*D_) - 0.046*sn(M+F-2*D_) + 0.033*sn(F+2*D_) + 0.017*sn(2*M+F)
    sun = ephem_sun(d)
    elong = math.acos(clamp(math.cos(lat*DEG)*math.cos((lon-sun['lon'])*DEG), -1, 1))/DEG
    illum = clamp((1-math.cos(elong*DEG))/2, 0, 1)
    age = ((d-5.2597) % 29.530588853 + 29.530588853) % 29.530588853
    ra, dec = to_eq(math.cos(lat*DEG)*math.cos(lon*DEG), math.cos(lat*DEG)*math.sin(lon*DEG), math.sin(lat*DEG))
    return {'lon':lon,'lat':lat,'ra':ra,'dec':dec,'distKm':r*6378.14,'illum':illum,'age':age}

wanderers = []
SUNNOW = {'raH': 0.0, 'dec': 0.0}
def build_wanderers():
    global wanderers, SUNNOW
    d = (time.time()*1000 - 946728000000)/86400000
    sun = ephem_sun(d); SUNNOW = {'raH': sun['ra']/15, 'dec': sun['dec']}
    wanderers = []
    m = ephem_moon(d)
    wanderers.append({'kind':'moon','name':'The Moon','raH':m['ra']/15,'dec':m['dec'],'illum':m['illum'],
                      'age':m['age'],'waxing':m['age'] < 14.765,'distKm':m['distKm'],
                      'phaseName':phase_name(m['age']),'ph':random.random()*6.28})
    for p in PLANETS:
        xh, yh, zh = kepler(p['el'], d)
        xg = xh + sun['dist']*math.cos(sun['lon']*DEG)
        yg = yh + sun['dist']*math.sin(sun['lon']*DEG)
        ra, dec = to_eq(xg, yg, zh)
        sep = angSep({'ra':ra/15,'dec':dec}, SUNNOW)
        wanderers.append({'kind':'planet','name':p['name'],'col':p['col'],'mag':p['mag'],'note':p['note'],
                          'au':math.hypot(xg, yg, zh),'raH':ra/15,'dec':dec,'glare':sep < 16,
                          'ph':random.random()*6.28})

def astro():
    d = (time.time()*1000 - 946728000000)/86400000
    return d, (280.46061837 + 360.98564736629*d) % 360
def alt_of(lat, lon, raDeg, dec, ast):
    d, g = ast
    lst = (g + lon + 360) % 360
    H = (lst - raDeg + 540) % 360 - 180
    alt = math.asin(clamp(math.sin(lat*DEG)*math.sin(dec*DEG) +
                          math.cos(lat*DEG)*math.cos(dec*DEG)*math.cos(H*DEG), -1, 1))/DEG
    altMax = 90-abs(lat-dec); altMin = lat+dec-90
    H0 = math.acos(clamp(-math.tan(lat*DEG)*math.tan(dec*DEG), -1, 1))/DEG
    rise = None; transit = ((-H) if H < 0 else (360-H))/15
    if abs(H) < 7.5: transit = 0
    if altMin <= 0 and altMax >= 0:
        if H < 0 and -H > H0: rise = (-H0-H)/15
        elif H > 0 and H > H0: rise = (360-H0-H)/15
    azS = math.atan2(math.sin(H*DEG), math.cos(H*DEG)*math.sin(lat*DEG)-math.tan(dec*DEG)*math.cos(lat*DEG))/DEG
    return {'alt':alt,'rise':rise,'transit':transit,'always':altMin > 0,'never':altMax < 0,'az':rev(azS+180)}
def sky_status(a):
    if a['never']: return 'never rises from this latitude'
    if a['always']:
        return ('well placed — it never sets' if a['alt'] > 25 else
                'low — it never sets' if a['alt'] > 0 else 'below the horizon — but it never truly sets')
    if a['alt'] > 60: return 'near the zenith'
    if a['alt'] > 25: return 'well placed'
    if a['alt'] > 0: return 'low on the horizon'
    return ('below the horizon — rises in '+fmtH(a['rise'])) if a['rise'] is not None else 'below the horizon'

BORTLE = [
 {'n':'Pristine dark','b':'Bortle 1 · a moonless desert or the open sea','lim':7.0,'mw':1.0,'glow':0,
  'msg':'Pristine dark — Bortle 1. The whole sky is yours, as nearly everyone saw it for most of history.'},
 {'n':'Rural dark','b':'Bortle 3 · the true countryside','lim':6.4,'mw':0.72,'glow':0.07,
  'msg':'Rural dark — Bortle 3. The Milky Way still casts a faint shadow here.'},
 {'n':'Suburban sky','b':'Bortle 5 · the edge of town','lim':5.5,'mw':0.4,'glow':0.17,
  'msg':'Suburban sky — Bortle 5. The faint river of the Milky Way begins to wash out.'},
 {'n':'Small city','b':'Bortle 7 · the glow hides the river','lim':4.6,'mw':0.18,'glow':0.32,
  'msg':'Small city — Bortle 7. The Milky Way is gone; only brighter stars survive.'},
 {'n':'Downtown','b':'Bortle 9 · twenty stars remain','lim':3.6,'mw':0.07,'glow':0.52,
  'msg':'Downtown — Bortle 9. Twenty stars and the wanderers remain. This is why dark places matter.'}]

# ============================== sound & speech (optional) ==============================
class Snd:
    SCALE = [220, 261.63, 293.66, 329.63, 392, 440, 523.25, 587.33, 659.25, 783.99, 880, 1046.5]
    def __init__(self):
        self.ok = False; self.muted = False; self.sink = None; self.io = None
        try:
            from PySide6.QtMultimedia import QAudioSink, QAudioFormat, QMediaDevices
            fmt = QAudioFormat(); fmt.setSampleRate(44100); fmt.setChannelCount(1)
            fmt.setSampleFormat(QAudioFormat.SampleFormat.Int16)
            dev = QMediaDevices.defaultAudioOutput()
            if dev is not None and not dev.isNull():
                self.sink = QAudioSink(dev, fmt); self.io = self.sink.start(); self.ok = True
        except Exception:
            pass
    def set_muted(self, m):
        self.muted = m
        if self.ok:
            try: self.sink.setVolume(0.0 if m else 0.9)
            except Exception: pass
    def _tone(self, f, peak, dur):
        if not self.ok or self.muted: return
        try:
            n = int(44100*dur); buf = array.array('h')
            for i in range(n):
                t = i/44100.0
                env = peak*math.exp(-3.2*t/dur)
                if t < 0.02: env *= t/0.02
                buf.append(int(32767*env*math.sin(2*math.pi*f*t)))
            self.io.write(buf.tobytes())
        except Exception:
            pass
    def note(self, i):
        f = self.SCALE[i % 12]; self._tone(f, 0.32, 0.9); self._tone(f*2.004, 0.07, 0.5)
    def tick(self): self._tone(1450, 0.10, 0.06)
    def thud(self): self._tone(92, 0.55, 0.5); self._tone(61, 0.3, 0.7)
    def dark(self): self._tone(110, 0.3, 2.5); self._tone(116.5, 0.22, 2.5); self._tone(55, 0.32, 3.0)
    def chord(self):
        for f in (220, 277.18, 329.63, 440): self._tone(f, 0.14, 3.5)

class Tts:
    def __init__(self):
        self.eng = None; self.speaking = False
        try:
            from PySide6.QtTextToSpeech import QTextToSpeech
            self.eng = QTextToSpeech()
            self.eng.stateChanged.connect(
                lambda s: setattr(self, 'speaking', s == QTextToSpeech.State.Speaking))
        except Exception:
            pass
    def available(self): return self.eng is not None
    def speak(self, text):
        if not self.eng: return False
        self.eng.stop(); self.eng.say(text); self.speaking = True; return True
    def stop(self):
        if self.eng: self.eng.stop()
        self.speaking = False

# ============================== save ==============================
SAVE_PATH = os.path.join(os.path.expanduser('~'), '.asterisma.json')
def normalize_save(s):
    o = {'done':{}, 'muted':False, 'seen':False, 'dark':False, 'grid':False, 'ach':{}, 'read':{},
         'seenObj':{}, 'pleiad':{}, 'trial':0, 'best':{}, 'geo':None, 'sq':0}
    if not isinstance(s, dict): return o
    for k in ('muted','seen','dark','grid'): o[k] = bool(s.get(k))
    t = s.get('trial', 0)
    o['trial'] = int(t) if isinstance(t, (int, float)) and 0 <= t <= 3 else 0
    q = s.get('sq', 0)
    o['sq'] = int(q) if isinstance(q, (int, float)) and 0 <= q <= len(BORTLE)-1 else 0
    for k in ('ach','read','seenObj','pleiad','done','best'):
        v = s.get(k)
        if isinstance(v, dict): o[k] = v
    done = {}
    for lv in LEVELS:
        d = o['done'].get(lv['id'])
        if isinstance(d, dict):
            done[lv['id']] = {'stars': clamp(int(d.get('stars') or 0), 0, 3),
                              'lapses': max(0, int(d.get('lapses') or 0)), 'dark': bool(d.get('dark'))}
    o['done'] = done
    best = {}
    for lv in LEVELS:
        b = o['best'].get(lv['id'])
        if isinstance(b, (int, float)) and 0 < b < 3600: best[lv['id']] = b
    o['best'] = best
    g = s.get('geo')
    if isinstance(g, dict) and isinstance(g.get('lat'), (int, float)) and isinstance(g.get('lon'), (int, float)) \
       and -90 <= g['lat'] <= 90 and -180 <= g['lon'] <= 180:
        o['geo'] = {'lat': g['lat'], 'lon': g['lon']}
    return o
def load_save():
    try:
        with open(SAVE_PATH, 'r', encoding='utf-8') as f:
            return normalize_save(json.load(f))
    except Exception:
        return normalize_save(None)
def persist(save):
    try:
        with open(SAVE_PATH, 'w', encoding='utf-8') as f:
            json.dump(save, f)
    except Exception:
        pass

ACHS = [
 ('firstlight','First Light','Chart your first figure.','✦'),
 ('steadyhand','Steady Hand','Chart a figure without one false line.','⊕'),
 ('untarnished','Untarnished','Chart every plate in the atlas flawlessly.','★'),
 ('storykeeper','Storykeeper','Read every tale the atlas holds.','📖'),
 ('deepeyes','Deep Eyes','Observe eight different hidden objects.','🔭'),
 ('lostpleiad','The Lost Pleiad','Find the two faint sisters of the Pleiades.','✧'),
 ('darklight','By Dark Alone','Chart a figure with dark-sky mode on.','☾'),
 ('vault','Vault-Walker','Walk the whole vault, every figure alight at once.','🌐'),
 ('listener','Told Aloud','Hear a tale spoken by the atlas.','🗣'),
 ('skywise','Sky-Watcher','Set your skies in Tonight’s Sky.','⌖'),
 ('island','Island Universe','Observe the Andromeda Galaxy.','◌'),
 ('wanderer','The Wanderers','Meet a wandering planet in the live sky.','🪐'),
 ('finder','By Name','Summon a star with the finder.','⌕'),
 ('citylight','City Astronomer','Chart a figure under a downtown sky.','🏙'),
 ('keepsake','The Keepsake','Take the finished atlas as a poster.','🖼'),
 ('master','Master Navigator','Earn gold in the Navigator’s Trial.','⏱')]

# ============================== sprite cache ==============================
class Sprites:
    def __init__(self):
        self.star = {}; self.soft = {}; self.ember = None
    def star_pix(self, col):
        pm = self.star.get(col)
        if pm is not None: return pm
        pm = QPixmap(96, 96); pm.fill(Qt.transparent)
        p = QPainter(pm); r, g, b = hexRGB(col)
        gr = QRadialGradient(48, 48, 48)
        gr.setColorAt(0.0, QColor(255, 255, 255, 255))
        gr.setColorAt(0.10, QColor(col))
        gr.setColorAt(0.32, QColor(r, g, b, 82))
        gr.setColorAt(1.0, QColor(0, 0, 0, 0))
        p.setRenderHint(QPainter.Antialiasing)
        p.fillRect(0, 0, 96, 96, QBrush(gr)); p.end()
        self.star[col] = pm; return pm
    def soft_pix(self, rgb):
        pm = self.soft.get(rgb)
        if pm is not None: return pm
        pm = QPixmap(128, 128); pm.fill(Qt.transparent)
        p = QPainter(pm)
        gr = QRadialGradient(64, 64, 64)
        gr.setColorAt(0.0, QColor('rgba(%s,255)' % rgb))
        gr.setColorAt(1.0, QColor('rgba(%s,0)' % rgb))
        p.fillRect(0, 0, 128, 128, QBrush(gr)); p.end()
        self.soft[rgb] = pm; return pm
    def ember_pix(self):
        if self.ember is not None: return self.ember
        pm = QPixmap(96, 96); pm.fill(Qt.transparent)
        p = QPainter(pm)
        gr = QRadialGradient(48, 48, 48)
        gr.setColorAt(0.0, QColor(232, 200, 119, 216))
        gr.setColorAt(0.35, QColor(201, 162, 74, 56))
        gr.setColorAt(1.0, QColor(201, 162, 74, 0))
        p.fillRect(0, 0, 96, 96, QBrush(gr)); p.end()
        self.ember = pm; return pm
SPR = Sprites()

def draw_blob(p, x, y, r, rgb, a):
    p.save(); p.setOpacity(max(0.0, min(1.0, a)))
    p.setRenderHint(QPainter.SmoothPixmapTransform)
    p.drawPixmap(QRectF(x-r, y-r, r*2, r*2), SPR.soft_pix(rgb), QRectF(0, 0, 128, 128))
    p.restore()
def draw_moon_disc(p, x, y, r, illum, waxing, halo):
    if halo: draw_blob(p, x, y, r*2.7, '230,226,210', 0.3)
    p.save(); p.setRenderHint(QPainter.Antialiasing)
    path = QPainterPath(); path.addEllipse(QPointF(x, y), r, r); p.setClipPath(path)
    p.setPen(Qt.NoPen)
    p.setBrush(QColor('#0c1220')); p.drawRect(QRectF(x-r, y-r, r*2, r*2))
    p.setBrush(QColor('#e7e2d0'))
    if waxing: p.drawChord(QRectF(x-r, y-r, r*2, r*2), -90*16, 180*16)
    else:      p.drawChord(QRectF(x-r, y-r, r*2, r*2), 90*16, 180*16)
    rx = max(0.001, r*abs(1-2*illum))
    p.setBrush(QColor('#e7e2d0') if illum > 0.5 else QColor('#0c1220'))
    p.drawEllipse(QPointF(x, y), rx, r)
    if r > 6:
        p.setBrush(QColor(90, 96, 116, 90))
        p.drawEllipse(QPointF(x-r*0.3, y-r*0.25), r*0.22, r*0.22)
        p.drawEllipse(QPointF(x+r*0.15, y+r*0.10), r*0.30, r*0.30)
        p.drawEllipse(QPointF(x-r*0.10, y+r*0.40), r*0.16, r*0.16)
    p.restore()
    p.save(); p.setRenderHint(QPainter.Antialiasing)
    p.setPen(QPen(QColor(231, 221, 196, 115), 1)); p.setBrush(Qt.NoBrush)
    p.drawEllipse(QPointF(x, y), r, r); p.restore()

# ============================== the sky view ==============================
METCOLS = ['240,244,255', '191,242,228', '255,231,189']

def sq_factor(mag, sq):
    B = BORTLE[sq]
    if mag <= B['lim']-1: return 1.0
    if mag >= B['lim']: return 0.0
    return B['lim']-mag

class SkyView(QWidget):
    def __init__(self, main):
        super().__init__()
        self.main = main
        self.setMouseTracking(True)
        self.setFocusPolicy(Qt.StrongFocus)
        self.cfg = OVERTURE
        self.cam = {'ra': 12.0, 'dec': 20.0, 'view': 110.0}
        self.ppd = 30.0; self.W = 10; self.H = 10
        self.phase = 'title'
        self.named = []; self.fuzzies = []
        self.field = []; self.twk = []; self.mwb = []; self.rift = []
        self.genHalfH = 30.0; self.genRaHalf = 6.0
        self.bg = None; self.dirty = True
        self.drawn = []; self.drawn_set = set(); self.edge_set = set()
        self.embers = 0; self.lapses = 0
        self.complete_at = 0.0; self.breath_at = 0.0; self.chart_start = 0.0
        self.sel = None; self.hover = None; self.focus_star = None
        self.hint = None; self.fizz = []; self.fizz_lines = []
        self.sparks = []; self.meteors = []; self.labels = {}; self.played = set()
        self.fly = None; self.drift = 0.0; self.tdrift = 0.0
        self.shake_at = -9.0
        self.mx = 0; self.my = 0
        self._press = None; self._moved = False; self._last_pick = 0.0
        self._panning = False
        self.next_meteor = 6.0; self.shower_until = 0.0
        self.tooltip = QLabel(self); self.tooltip.setObjectName('tipBox')
        self.tooltip.setWordWrap(True); self.tooltip.hide(); self.tooltip.setAttribute(Qt.WA_TransparentForMouseEvents)
        self.timer = QTimer(self); self.timer.timeout.connect(self.tick)
        self.timer.start(33)
        self._t0 = time.perf_counter()
        self.refresh_field()

    # ---------- camera / config ----------
    def proj(self, ra, dec):
        x = self.W/2 + (ra-self.cam['ra'] - round((ra-self.cam['ra'])/24.0)*24.0) * 15 * math.cos(self.cam['dec']*DEG) * self.ppd
        y = self.H/2 - (dec-self.cam['dec'])*self.ppd
        return x, y
    def unproj(self, x, y):
        ra = self.cam['ra'] + (x-self.W/2)/(self.ppd*15*max(0.1, math.cos(self.cam['dec']*DEG)))
        return ra % 24.0, self.cam['dec'] - (y-self.H/2)/self.ppd
    def clamp_cam(self):
        cfg = self.cfg
        if cfg.get('tour'): return
        cosd = max(0.15, math.cos(self.cam['dec']*DEG))
        visH = (self.W/2)/(15*cosd*self.ppd); visD = (self.H/2)/self.ppd
        raLim = max(0.01, self.genRaHalf-visH); decLim = max(0.01, self.genHalfH-visD)
        cx, cy = cfg['center']
        self.cam['dec'] = clamp(self.cam['dec'], cy-decLim, cy+decLim)
        self.cam['ra'] = mod24(cx + clamp(deltaH(self.cam['ra'], cx), -raLim, raLim))
    def set_cam(self, ra, dec, view):
        self.cam = {'ra': ra, 'dec': dec, 'view': view}
        self.ppd = min(self.W, self.H)/view if min(self.W, self.H) > 0 else 30
        self.clamp_cam(); self.dirty = True
    def zoom_at(self, x, y, z):
        self.fly = None
        cfg = self.cfg
        before = self.unproj(x, y)
        self.cam['view'] = clamp(self.cam['view']/z, cfg['viewMin']*cfg['view'], cfg['view']*1.45)
        self.ppd = min(self.W, self.H)/self.cam['view']
        after = self.unproj(x, y)
        self.cam['ra'] = mod24(self.cam['ra'] + before[0]-after[0])
        self.cam['dec'] += before[1]-after[1]
        self.clamp_cam(); self.dirty = True
        self.main.upd_field_label()
    def pan_by(self, dx, dy):
        self.fly = None
        self.cam['ra'] = mod24(self.cam['ra'] - dx/(15*max(0.15, math.cos(self.cam['dec']*DEG))*self.ppd))
        self.cam['dec'] += dy/self.ppd
        self.clamp_cam(); self.dirty = True
        self.main.upd_field_label()
    def reset_view(self):
        self.fly = None
        self.set_cam(self.cfg['center'][0], self.cfg['center'][1], self.cfg['view'])
        self.main.upd_field_label()
    def fly_to(self, ra, dec, view=None):
        cfg = self.cfg
        v = clamp(view if view else self.cam['view'], cfg['viewMin']*cfg['view'], cfg['view']*1.45)
        self.fly = {'t0': time.perf_counter(), 'dur': 0.35 if self.main.reduced else 0.9,
                    'f': dict(self.cam), 't': {'ra': ra % 24.0, 'dec': dec, 'view': v}}

    def load_config(self, cfg, explore=False):
        self.cfg = cfg; self.cfg['explore'] = explore
        self.phase = 'playing'
        self.fly = None; self.drift = 0.0
        self.sel = None; self.hover = None; self.focus_star = None
        self.hint = None; self.fizz = []; self.fizz_lines = []; self.sparks = []
        self.labels = {}; self.played = set(); self.complete_at = 0.0
        self.lapses = 0; self.embers = cfg['embers']
        self.chart_start = time.perf_counter()
        self.edge_set = set(ekey(a, b) for a, b in cfg['edges'])
        self.drawn = []; self.drawn_set = set()
        self.named = cfg['stars']
        for s in self.named: s['ph'] = random.random()*6.28
        self.fuzzies = cfg.get('fuzzy') or []
        if explore:
            self.drawn = [{'a': a, 'b': b, 't0': 0.0} for a, b in cfg['edges']]
            self.drawn_set = set(self.edge_set)
        self.set_cam(cfg['center'][0], cfg['center'][1], cfg['view'])
        self.refresh_field()
        self.breath_at = time.perf_counter()

    def refresh_field(self):
        self.build_field(self.cfg)
        self.clamp_cam(); self.dirty = True

    def build_field(self, cfg):
        rng = mulberry32(((cfg['seed']*2654435761) & 0xFFFFFFFF) ^ 0x9e37)
        self.field = []; self.twk = []; self.mwb = []; self.rift = []
        def pick_col():
            q = rng()
            return ('#dfe6f5' if q < 0.68 else '#c9d6ff' if q < 0.8 else
                    '#fff2d4' if q < 0.88 else '#ffd9a0' if q < 0.95 else '#ffab73')
        def push(ra, dec, mag):
            r = clamp(0.45+(5.4-mag)*0.3, 0.35, 1.4)
            a = clamp(0.5-(mag-4)*0.09, 0.08, 0.5)+rng()*0.14
            o = {'ra': ra, 'dec': dec, 'r': r, 'a': a, 'col': pick_col(), 'mag': mag}
            if rng() < 0.25 and mag < 5.7:
                o['sp'] = 0.6+rng()*1.7; o['ph'] = rng()*6.28; self.twk.append(o)
            else: self.field.append(o)
        cx, cy = cfg['center']
        if cfg.get('tour'):
            for _ in range(1400):
                push(cx+(rng()*2-1)*14.5, math.asin(rng()*2-1)/DEG, 3.5+rng()*3.5)
        else:
            F = cfg['view']*1.45
            arW = self.W/max(1, min(self.W, self.H)); arH = self.H/max(1, min(self.W, self.H))
            self.genHalfH = (F/2)*arH*1.15
            cosC = max(0.2, math.cos(cy*DEG))
            visHmax = (F/2)*arW/(15*cosC)
            decWorst = min(88, abs(cy)+self.genHalfH)
            cosW = max(0.16, math.cos(decWorst*DEG))
            self.genRaHalf = min(10, visHmax*(cosC/cosW)*1.15)
            nS = int(clamp(self.W*self.H/8500*2.2, 320, 900))
            for _ in range(nS):
                push(cx+(rng()*2-1)*self.genRaHalf,
                     clamp(cy+(rng()*2-1)*self.genHalfH, -89, 89), 3.9+rng()*3.1)
            if cfg.get('deep'):
                hW = (cfg['view']/2)*arW/(15*cosC); hD = (cfg['view']/2)*arH
                for _ in range(cfg['deep']):
                    push(cx+(rng()*2-1)*hW, cy+(rng()*2-1)*hD, 5.6+rng()*2.8)
        mw = cfg.get('mw')
        if mw:
            P = mw['pts']; halfDeg = mw['width']*cfg['view']*0.5
            def off_at(t):
                p1 = qbez(P, min(0.999, t+0.001)); p0 = qbez(P, max(0.001, t-0.001))
                dx = (p1[0]-p0[0])*15*max(0.25, math.cos(p1[1]*DEG)); dy = p1[1]-p0[1]
                Lm = math.hypot(dx, dy) or 1
                return (-dy/Lm, dx/Lm)
            def put(t, sdeg, fn):
                ra, dec = qbez(P, t); o = off_at(t); s = gauss_of(rng)*sdeg
                fn(rev(ra + o[0]*s/(15*max(0.25, math.cos(dec*DEG)))), dec+o[1]*s)
            t = 0.03
            while t <= 0.98:
                put(t, halfDeg*0.25, lambda ra, dec: self.mwb.append(
                    {'ra': ra, 'dec': dec, 'rDeg': halfDeg*(0.75+0.6*rng()),
                     'a': (0.016+0.02*rng())*mw['glow']}))
                t += 0.055+0.045*rng()
            if mw['rift']:
                for t2 in [0.15+i*0.06 for i in range(12)]:
                    if t2 > 0.85: break
                    put(t2, halfDeg*0.3, lambda ra, dec: self.rift.append(
                        {'ra': ra, 'dec': dec, 'rDeg': halfDeg*0.42}))
            for _ in range(int(340*mw['glow'])):
                t3 = rng()
                def mk(ra, dec):
                    mag = 4.6+rng()*2.8
                    r = clamp(0.4+(5.4-mag)*0.32, 0.35, 1.3)
                    a = clamp(0.42-(mag-4)*0.09, 0.08, 0.4)
                    o = {'ra': ra, 'dec': dec, 'r': r, 'a': a, 'mag': mag,
                         'col': '#dfe6f5' if rng() < 0.8 else '#c9d6ff'}
                    if rng() < 0.15:
                        o['sp'] = 0.6+rng()*1.6; o['ph'] = rng()*6.28; self.twk.append(o)
                    else: self.field.append(o)
                put(t3, halfDeg*0.5, mk)

    def rebuild_bg(self):
        dpr = self.devicePixelRatioF()
        Wd, Hd = int(self.W*dpr)+1, int(self.H*dpr)+1
        img = QImage(Wd, Hd, QImage.Format_ARGB32_Premultiplied)
        img.setDevicePixelRatio(dpr)
        p = QPainter(img); p.setRenderHint(QPainter.Antialiasing)
        p.setRenderHint(QPainter.SmoothPixmapTransform)
        p.fillRect(0, 0, self.W, self.H, QColor('#050a14'))
        cfg = self.cfg; B = BORTLE[self.main.save.get('sq', 0)]
        for b in self.mwb:
            x, y = self.proj(b['ra'], b['dec'])
            draw_blob(p, x, y, b['rDeg']*self.ppd*1.8, '205,216,242', b['a']*0.35*B['mw'])
        for b in self.mwb:
            x, y = self.proj(b['ra'], b['dec'])
            draw_blob(p, x, y, b['rDeg']*self.ppd, '205,216,242', b['a']*B['mw'])
        for b in self.rift:
            x, y = self.proj(b['ra'], b['dec'])
            draw_blob(p, x, y, b['rDeg']*self.ppd, '5,10,20', 0.3*B['mw'])
        for n in cfg.get('neb') or []:
            x, y = self.proj(n['ra'], n['dec'])
            draw_blob(p, x, y, n['r']*2*self.ppd, n['col'], n['a']*B['mw'])
        for f in self.fuzzies:
            if 'blob' in f:
                x, y = self.proj(f['ra'], f['dec'])
                draw_blob(p, x, y, f['blob'][0]*2*self.ppd, f['blob'][1], f['blob'][2]*B['mw'])
        for o in self.field:
            f = sq_factor(o['mag'], self.main.save.get('sq', 0))
            if f <= 0.02: continue
            x, y = self.proj(o['ra'], o['dec'])
            if x < -24 or x > self.W+24 or y < -24 or y > self.H+24: continue
            p.setOpacity(o['a']*f)
            p.drawPixmap(QRectF(x-o['r']*6, y-o['r']*6, o['r']*12, o['r']*12),
                         SPR.star_pix(o['col']), QRectF(0, 0, 96, 96))
        p.setOpacity(1)
        if B['glow'] > 0:
            gr = QLinearGradient(0, self.H, 0, 0)
            gr.setColorAt(0, QColor(66, 48, 30, int(255*B['glow']*0.85)))
            gr.setColorAt(1, QColor(66, 48, 30, int(255*B['glow']*0.30)))
            p.fillRect(0, 0, self.W, self.H, QBrush(gr))
        vg = QRadialGradient(self.W/2, self.H/2, max(self.W, self.H)*0.75)
        vg.setInnerRadius(min(self.W, self.H)*0.38)
        vg.setColorAt(0, QColor(2, 4, 10, 0)); vg.setColorAt(1, QColor(2, 4, 10, 140))
        p.fillRect(0, 0, self.W, self.H, QBrush(vg))
        p.end()
        self.bg = img; self.dirty = False

    # ---------- picking ----------
    def pick_at(self, x, y):
        best = None; bd = 1e9
        for s in self.named:
            d = math.hypot(s.get('_x', -1e9)-x, s.get('_y', -1e9)-y)
            if d < max(16, s.get('_r', 5)+8) and d < bd: bd = d; best = s
        for w in wanderers:
            if '_x' not in w: continue
            d = math.hypot(w['_x']-x, w['_y']-y)
            if d < max(15, w.get('_r', 6)+9) and d < bd: bd = d; best = w
        if best is None:
            for f in self.fuzzies:
                fx, fy = self.proj(f['ra'], f['dec']); f['_x'] = fx; f['_y'] = fy
                d = math.hypot(fx-x, fy-y)
                if d < 15 and d < bd: bd = d; best = f
        return best

    # ---------- game ----------
    def select_star(self, s):
        self.sel = s; self.main.snd.tick()
        self.main.set_sel_label(s)
    def clear_sel(self):
        self.sel = None; self.main.set_sel_label(None)
    def attempt(self, a, b):
        if self.phase != 'playing': return
        if self.cfg.get('explore'):
            self.main.toast('The lines are already drawn — this is a study chart.'); return
        if self.cfg.get('tour'):
            self.main.toast('The vault is already fully charted.'); return
        key = ekey(a['id'], b['id'])
        if key in self.drawn_set:
            self.main.toast('That line is already charted.'); return
        if key in self.edge_set:
            self.drawn.append({'a': a['id'], 'b': b['id'], 't0': time.perf_counter()})
            self.drawn_set.add(key)
            self.main.snd.note(len(self.drawn)-1)
            self.labels[a['id']] = time.perf_counter(); self.labels[b['id']] = time.perf_counter()
            self.main.update_hud()
            if len(self.drawn) == len(self.cfg['edges']): self.on_complete()
        else:
            self.lapses += 1; self.embers -= 1
            self.main.snd.thud(); self.shake_at = time.perf_counter()
            self.fizz_lines.append({'a': a['id'], 'b': b['id'], 't0': time.perf_counter()})
            x1, y1 = self.proj(a['ra'], a['dec']); x2, y2 = self.proj(b['ra'], b['dec'])
            for _ in range(16):
                q = random.random()
                self.fizz.append({'x': x1+(x2-x1)*q, 'y': y1+(y2-y1)*q,
                                  'vx': (random.random()-0.5)*46, 'vy': (random.random()-0.5)*46,
                                  'born': time.perf_counter()})
            self.main.update_hud()
            if self.embers <= 0:
                self.phase = 'fading'
                QTimer.singleShot(900, self.main.night_dims)
            else:
                self.main.toast('An ember gutters out — %d remain%s.' %
                                (self.embers, '' if self.embers == 1 else 's'))
    def on_complete(self):
        self.phase = 'complete'; self.complete_at = time.perf_counter()
        self.clear_sel(); self.focus_star = None; self.hint = None
        self.main.on_plate_complete()

    # ---------- events ----------
    def resizeEvent(self, ev):
        dpr = self.devicePixelRatioF()
        self.W = max(1, int(self.width())); self.H = max(1, int(self.height()))
        self.ppd = min(self.W, self.H)/self.cam['view']
        self.dirty = True
        super().resizeEvent(ev)
    def wheelEvent(self, ev):
        d = ev.angleDelta().y()
        if d: self.zoom_at(ev.position().x(), ev.position().y(), 1.15 if d > 0 else 1/1.15)
    def mousePressEvent(self, ev):
        if ev.button() != Qt.LeftButton: return
        self._press = (ev.position().x(), ev.position().y())
        self._moved = False
        self._down_hit = None
        if self.main.modal_open(): return
        self._down_hit = self.pick_at(*self._press)
    def mouseMoveEvent(self, ev):
        x, y = ev.position().x(), ev.position().y()
        self.mx, self.my = x, y
        ra, dec = self.unproj(x, y)
        self.main.set_coords(ra, dec)
        if self._press is not None:
            dx, dy = x-self._press[0], y-self._press[1]
            if not self._moved and math.hypot(dx, dy) > 6:
                self._moved = True; self._panning = True
                self.setCursor(Qt.ClosedHandCursor); self.hide_tip()
            if self._moved:
                self.pan_by(x-(self._last or x), y-(self._lasty or y))
        self._last, self._lasty = x, y
        if not self._panning and not self.main.modal_open():
            h = self.pick_at(x, y)
            self.hover = h
            if h is not None: self.show_tip(h, x, y)
            else: self.hide_tip()
            self.main.update_sep()
    def mouseReleaseEvent(self, ev):
        if ev.button() != Qt.LeftButton: return
        was_moved = self._moved
        self._press = None; self._panning = False
        self.setCursor(Qt.CrosshairCursor)
        if not was_moved and not self.main.modal_open() and self.phase == 'playing':
            p = self._down_hit
            if p is None or (not p.get('id') and 'kind' not in p): self.clear_sel()
            elif 'kind' in p: self.clear_sel()   # wanderers are for looking, not drawing
            else:
                self._last_pick = time.perf_counter()
                if self.sel is None: self.select_star(p)
                elif self.sel is p: self.clear_sel()
                else:
                    a, b = self.sel, p; self.clear_sel(); self.attempt(a, b)
        self._down_hit = None; self._moved = False
    def mouseDoubleClickEvent(self, ev):
        if time.perf_counter()-self._last_pick < 0.4: return
        self.reset_view()
    def leaveEvent(self, ev):
        self.hide_tip(); self.hover = None; super().leaveEvent(ev)

    def show_tip(self, s, x, y):
        if 'kind' in s and s['kind'] == 'moon':
            advice = ('Its light washes out the faintest stars — a night for the bright figures.'
                      if s['illum'] > 0.66 else
                      'A moonless night — the faint things are yours tonight.' if s['illum'] < 0.15 else
                      'Gentle moonlight — faint objects remain within reach, away from the Moon.')
            html = ('<b><i>The Moon</i></b><br>%s · %d%% lit<br>'
                    '<span class=m>%s km away</span><br><i>%s</i>' %
                    (s['phaseName'], round(s['illum']*100),
                     format(round(s['distKm']), ','), advice))
        elif 'kind' in s and s['kind'] == 'planet':
            html = ('<b><i>%s</i></b><br>a wandering star — a planet · ≈ mag %.1f<br>'
                    '<span class=m>%.2f AU away%s</span><br><i>%s</i>' %
                    (s['name'], s['mag'], s['au'],
                     ' · lost in the Sun’s glare' if s.get('glare') else '', s['note']))
            self.main.grant('wanderer')
        elif s.get('info') and not s.get('bayer'):
            html = '<b><i>%s</i></b><br><i>%s</i>' % (s['name'], s['info'])
        else:
            html = ('<b><i>%s</i></b><br>%s · <span style="color:%s">●</span> %s<br>'
                    '<span class=m>mag %.2f · %s</span>%s' %
                    (s['name'], s['bayer'], SPEC[s['cls']], s['spec'], s['mag'], s['dist'],
                     ('<br><i>%s</i>' % s['info']) if s.get('info') else ''))
            nm = s['name']
            if not self.cfg.get('tour'):
                so = self.main.save.setdefault('seenObj', {})
                if (nm not in so) and (not s.get('bayer') or nm in ('Celaeno', 'Asterope')):
                    so[nm] = 1; persist(self.main.save)
                    if len(so) >= 8: self.main.grant('deepeyes')
                    if nm in ('Celaeno', 'Asterope'):
                        pl = self.main.save.setdefault('pleiad', {}); pl[nm] = 1; persist(self.main.save)
                        if 'Celaeno' in pl and 'Asterope' in pl: self.main.grant('lostpleiad')
                if nm.startswith('M31'): self.main.grant('island')
        self.tooltip.setText(html)
        self.tooltip.adjustSize()
        w = self.tooltip.width(); h = self.tooltip.height()
        self.tooltip.move(int(clamp(x+16, 4, self.W-w-4)), int(clamp(y+18, 4, self.H-h-4)))
        self.tooltip.show(); self.tooltip.raise_()
    def hide_tip(self):
        self.tooltip.hide()

    # ---------- animation tick ----------
    def tick(self):
        tn = time.perf_counter()
        t = tn - self._t0
        if self.dirty: self.rebuild_bg()
        dt = 0.033
        main = self.main
        if self.phase == 'title' and not main.reduced:
            self.tdrift += 0.0022*dt
            if self.tdrift > 0.0005:
                self.cam['ra'] = mod24(self.cam['ra']+self.tdrift); self.tdrift = 0.0; self.dirty = True
        if self.cfg.get('tour') and self.phase == 'playing' and not main.reduced and not self._panning and self.fly is None:
            self.drift += 0.0028*dt
            if self.drift > 0.0005:
                self.cam['ra'] = mod24(self.cam['ra']+self.drift); self.drift = 0.0; self.dirty = True
        if self.fly:
            k = clamp((tn-self.fly['t0'])/self.fly['dur'], 0, 1); e = easeIO(k)
            f, to = self.fly['f'], self.fly['t']
            self.cam['ra'] = mod24(f['ra'] + deltaH(to['ra'], f['ra'])*e)
            self.cam['dec'] = f['dec'] + (to['dec']-f['dec'])*e
            self.cam['view'] = f['view']*math.pow(to['view']/f['view'], e)
            self.ppd = min(self.W, self.H)/self.cam['view']
            self.dirty = True; self.main.upd_field_label()
            if k >= 1: self.fly = None
        if not main.reduced:
            if t > self.next_meteor and len(self.meteors) < (6 if tn < self.shower_until else 2):
                self.meteors.append({'x': random.random()*self.W, 'y': random.random()*self.H*0.6,
                                     'vx': (1 if random.random() < .5 else -1)*(180+random.random()*160),
                                     'vy': 120+random.random()*100, 'born': tn,
                                     'col': METCOLS[random.randrange(3)]})
                self.next_meteor = t + (0.16 if tn < self.shower_until else 14+random.random()*22)
        self.meteors = [m for m in self.meteors if tn-m['born'] < 0.9]
        self.update()

    # ---------- painting ----------
    def paintEvent(self, ev):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        p.setRenderHint(QPainter.SmoothPixmapTransform)
        p.fillRect(self.rect(), QColor('#050a14'))
        tn = time.perf_counter(); t = tn - self._t0
        baseA = 1.0
        if self.phase == 'complete':
            baseA = 1-0.25*clamp((tn-self.complete_at)/0.9, 0, 1)
        if self.bg is not None:
            p.setOpacity(baseA); p.drawImage(0, 0, self.bg); p.setOpacity(1)
        p.save()
        if tn-self.shake_at < 0.26:
            m = (1-(tn-self.shake_at)/0.26)*3
            p.translate(math.sin(t*70)*m, math.cos(t*61)*m)
        sq = self.main.save.get('sq', 0)
        # twinkles
        tk = 0.5 if self.main.reduced else 1.0
        for s in self.twk:
            x, y = self.proj(s['ra'], s['dec'])
            if x < -16 or x > self.W+16 or y < -16 or y > self.H+16: continue
            f = sq_factor(s['mag'], sq)
            if f <= 0.02: continue
            p.setOpacity(baseA*s['a']*(0.82+0.18*math.sin(t*s['sp']+s['ph'])*tk)*f)
            p.drawPixmap(QRectF(x-s['r']*6, y-s['r']*6, s['r']*12, s['r']*12),
                         SPR.star_pix(s['col']), QRectF(0, 0, 96, 96))
        p.setOpacity(1)
        if self.cfg is not None and self.main.save.get('grid') and self.phase != 'title':
            self.draw_grid(p)
        # meteors
        for m in self.meteors:
            k = (tn-m['born'])/0.9; a = math.sin(math.pi*k)*0.55
            x2, y2 = m['x']-m['vx']*0.12, m['y']-m['vy']*0.12
            gr = QLinearGradient(m['x'], m['y'], x2, y2)
            gr.setColorAt(0, QColor('rgba(%s,%d)' % (m['col'], int(a*255))))
            gr.setColorAt(1, QColor('rgba(%s,0)' % m['col']))
            p.setPen(QPen(QBrush(gr), 1.1)); p.drawLine(QPointF(m['x'], m['y']), QPointF(x2, y2))
            m['x'] += m['vx']*0.033; m['y'] += m['vy']*0.033
        # figure centroid
        fig = [s for s in self.named if s.get('figure')]
        cx0 = cy0 = 0.0; miny = 1e9
        for s in fig:
            x, y = self.proj(s['ra'], s['dec']); s['_x'] = x; s['_y'] = y
            cx0 += x; cy0 += y; miny = min(miny, y)
        if fig: cx0 /= len(fig); cy0 /= len(fig)
        self.cx0, self.cy0, self.miny = cx0, cy0, miny
        rs = clamp(math.sqrt(self.ppd/30), 0.75, 1.8)
        for s in self.named:
            s['_r'] = clamp(0.9+(5.2-s['mag'])*1.05, 1.1, 8.5)*rs
        # lines
        if self.cfg:
            done = self.phase == 'complete' or self.cfg.get('explore') or self.cfg.get('tour')
            mp = self.cfg['map']
            for i, d in enumerate(self.drawn):
                a = mp.get(d['a']); b = mp.get(d['b'])
                if not a or not b: continue
                gold = flash = 0.0
                if done:
                    if self.phase == 'complete':
                        te = 0.30+i*0.14
                        gold = clamp((tn-self.complete_at-te)/0.35, 0, 1)
                        flash = max(0.0, 1-gold)
                        if gold > 0.4 and i not in self.played:
                            self.played.add(i); self.main.snd.note(i)
                    else: gold = 1.0
                prog = clamp((tn-d['t0'])/0.48, 0, 1) if d['t0'] else 1.0
                x1, y1 = self.proj(a['ra'], a['dec']); x2, y2 = self.proj(b['ra'], b['dec'])
                xe = x1+(x2-x1)*prog; ye = y1+(y2-y1)*prog
                if gold > 0:
                    p.setPen(QPen(QColor(232, 200, 119, int(33*gold)), 4.5))
                    p.drawLine(QPointF(x1, y1), QPointF(xe, ye))
                    p.setPen(QPen(QColor(236, 208, 140, int((0.8 if (self.cfg.get('explore') or self.cfg.get('tour')) else 0.95)*gold*255)), 1.3))
                else:
                    p.setPen(QPen(QColor(214, 226, 255, 184), 1.1))
                p.drawLine(QPointF(x1, y1), QPointF(xe, ye))
                if flash > 0:
                    p.setPen(QPen(QColor(255, 240, 200, int(flash*153)), 2.5))
                    p.drawLine(QPointF(x1, y1), QPointF(xe, ye))
            # fizz ghosts
            now2 = tn
            self.fizz_lines = [f for f in self.fizz_lines if now2-f['t0'] < 0.52]
            for f in self.fizz_lines:
                a = mp.get(f['a']); b = mp.get(f['b'])
                if not a or not b: continue
                k = 1-(now2-f['t0'])/0.52
                x1, y1 = self.proj(a['ra'], a['dec']); x2, y2 = self.proj(b['ra'], b['dec'])
                p.setPen(QPen(QColor(217, 95, 74, int(k*102)), 1))
                p.drawLine(QPointF(x1, y1), QPointF(x2, y2))
            self.fizz = [q for q in self.fizz if now2-q['born'] < 0.76]
            p.setPen(Qt.NoPen)
            for q in self.fizz:
                k = 1-(now2-q['born'])/0.76
                q['x'] += q['vx']*0.033; q['y'] += q['vy']*0.033
                p.setBrush(QColor(217, 95, 74, int(k*204)))
                p.drawEllipse(QPointF(q['x'], q['y']), 1.4, 1.4)
            p.setBrush(Qt.NoBrush)
            # hint
            if self.hint and tn < self.hint['until']:
                a, b = self.hint['a'], self.hint['b']
                x1, y1 = self.proj(a['ra'], a['dec']); x2, y2 = self.proj(b['ra'], b['dec'])
                pen = QPen(QColor(232, 200, 119, 90), 1, Qt.DashLine)
                pen.setDashOffset(-t*20); p.setPen(pen)
                p.drawLine(QPointF(x1, y1), QPointF(x2, y2))
                for s in (a, b):
                    x, y = self.proj(s['ra'], s['dec']); rk = (t*1.1) % 1
                    p.setPen(QPen(QColor(232, 200, 119, int((1-rk)*140)), 1))
                    p.drawEllipse(QPointF(x, y), s['_r']+4+rk*22, s['_r']+4+rk*22)
            else: self.hint = None
            # hidden pulses
            for f in self.fuzzies:
                x, y = self.proj(f['ra'], f['dec']); f['_x'] = x; f['_y'] = y
                al = 0.09+0.09*(0.5+0.5*math.sin(t*1.8))
                p.setPen(QPen(QColor(232, 200, 119, int(al*baseA*255)), 1))
                p.drawEllipse(QPointF(x, y), 6.5, 6.5)
        # wanderers
        if self.phase != 'title':
            for w in wanderers:
                x, y = self.proj(w['raH'], w['dec'])
                if x < -40 or x > self.W+40 or y < -40 or y > self.H+40: continue
                w['_x'] = x; w['_y'] = y
                if w['kind'] == 'moon':
                    r = clamp(self.ppd*0.24, 4.5, 12)*rs; w['_r'] = r
                    draw_blob(p, x, y, r*3, '232,228,212', 0.35*baseA)
                    p.setOpacity(baseA)
                    draw_moon_disc(p, x, y, r, w['illum'], w['waxing'], False)
                    p.setOpacity(1)
                    lab = 'Moon'
                else:
                    rr = clamp(3.4+(0.2-w['mag'])*1.2, 3.6, 7)*rs; w['_r'] = rr
                    draw_blob(p, x, y, rr*3, hexRGB(w['col']) and '%d,%d,%d' % hexRGB(w['col']), 0.5*baseA)
                    p.setOpacity(baseA)
                    p.setPen(Qt.NoPen); p.setBrush(QColor(w['col']))
                    p.drawEllipse(QPointF(x, y), rr, rr)
                    if w['mag'] < 0:
                        p.setPen(QPen(QColor(w['col'], 115), 1))
                        L2 = rr*4
                        p.drawLine(QPointF(x-L2, y), QPointF(x+L2, y))
                        p.drawLine(QPointF(x, y-L2), QPointF(x, y+L2))
                    p.setOpacity(1); lab = w['name']
                if self.cam['view'] < 70:
                    f = QFont(); f.setFamilies(['IBM Plex Mono', 'Consolas', 'monospace']); f.setPixelSize(9)
                    p.setFont(f); p.setPen(QColor(201, 162, 74, int(0.7*baseA*255)))
                    p.drawText(QPointF(x+w['_r']+6, y-4), lab)
        # named stars
        for s in self.named:
            x, y = self.proj(s['ra'], s['dec'])
            if x < -60 or x > self.W+60 or y < -60 or y > self.H+60: continue
            s['_x'] = x; s['_y'] = y
            r = s['_r']; tw = 1+0.05*math.sin(t*1.6+s.get('ph', 0))
            if s.get('figure'):
                bt = tn-self.breath_at
                a = (0.11+0.05*math.sin(t*1.4+s.get('ph', 0)))*(0.5 if self.main.save.get('dark') else 1)
                if bt < 3: a += (0.05 if self.main.save.get('dark') else 0.11)*abs(math.sin(bt*2.6))
                p.setOpacity(a*baseA)
                p.drawPixmap(QRectF(x-r*7, y-r*7, r*14, r*14), SPR.ember_pix(), QRectF(0, 0, 96, 96))
            vf = max(sq_factor(s['mag'], sq), 0.5) if s.get('figure') else max(sq_factor(s['mag'], sq), 0.12)
            p.setOpacity((1 if s.get('figure') else (0.55 if self.main.save.get('dark') else 0.92))*vf*baseA)
            p.drawPixmap(QRectF(x-r*6*tw, y-r*6*tw, r*12*tw, r*12*tw),
                         SPR.star_pix(SPEC[s['cls']]), QRectF(0, 0, 96, 96))
            if r > 3 and vf > 0.3:
                p.setPen(QPen(QColor(SPEC[s['cls']]), 1)); p.setOpacity(0.5*vf*baseA)
                L2 = r*5
                p.drawLine(QPointF(x-L2, y), QPointF(x+L2, y))
                p.drawLine(QPointF(x, y-L2), QPointF(x, y+L2))
            p.setOpacity(1)
        # selection & focus
        if self.phase == 'playing':
            if self.sel is not None and '_x' in self.sel:
                pen = QPen(QColor(232, 200, 119, 217), 1.2, Qt.DashLine)
                pen.setDashOffset(-t*14); p.setPen(pen); p.setBrush(Qt.NoBrush)
                p.drawEllipse(QPointF(self.sel['_x'], self.sel['_y']), self.sel['_r']+7, self.sel['_r']+7)
                snap = None
                if self.hover is not None and self.hover is not self.sel and 'name' in self.hover:
                    snap = self.hover
                else:
                    for s in self.named:
                        if s is self.sel: continue
                        if (s['_x']-self.mx)**2+(s['_y']-self.my)**2 < 18*18: snap = s; break
                if snap: tx, ty, col = snap['_x'], snap['_y'], QColor(232, 200, 119, 102)
                else: tx, ty, col = self.mx, self.my, QColor(232, 200, 119, 51)
                pen = QPen(col, 1, Qt.DashLine); pen.setDashOffset(-t*20); p.setPen(pen)
                p.drawLine(QPointF(self.sel['_x'], self.sel['_y']), QPointF(tx, ty))
            if self.focus_star is not None and '_x' in self.focus_star:
                p.setPen(QPen(QColor(232, 200, 119, 178), 1, Qt.DashLine)); p.setBrush(Qt.NoBrush)
                p.drawEllipse(QPointF(self.focus_star['_x'], self.focus_star['_y']),
                              self.focus_star['_r']+11, self.focus_star['_r']+11)
                self.draw_label(p, self.focus_star, 0.95)
        # labels
        if self.cfg:
            mp = self.cfg['map']
            for k in list(self.labels.keys()):
                s = mp.get(k); k2 = (tn-self.labels[k])/2.6
                if k2 >= 1 or not s or not s.get('figure'): del self.labels[k]; continue
                self.draw_label(p, s, math.sin(math.pi*k2)*0.9)
            if self.phase == 'complete':
                for i, s in enumerate(fig):
                    a = clamp((tn-self.complete_at-0.8-i*0.09)/0.5, 0, 1)*0.95
                    if a > 0: self.draw_label(p, s, a)
                rk = clamp((tn-self.complete_at-0.5)/1.0, 0, 1)
                if 0 < rk < 1:
                    p.setPen(QPen(QColor(232, 200, 119, int((1-rk)*128)), 1.5)); p.setBrush(Qt.NoBrush)
                    p.drawEllipse(QPointF(cx0, cy0), rk*280+10, rk*280+10)
                a2 = clamp((tn-self.complete_at-1.1)/0.8, 0, 1)*0.92
                if a2 > 0:
                    ly = clamp(miny-56, 80, self.H-20)
                    p.setOpacity(a2)
                    f = QFont(); f.setFamilies(['Fraunces', 'Georgia', 'serif'])
                    f.setItalic(True); f.setWeight(QFont.Light); f.setPixelSize(42)
                    p.setFont(f); p.setPen(QColor(236, 226, 200))
                    p.drawText(QPointF(cx0-p.fontMetrics().horizontalAdvance(self.cfg['name'])/2, ly),
                               self.cfg['name'])
                    f2 = QFont(); f2.setFamilies(['IBM Plex Mono', 'Consolas', 'monospace'])
                    f2.setPixelSize(10); f2.setLetterSpacing(QFont.AbsoluteSpacing, 4)
                    p.setFont(f2); p.setPen(QColor(201, 162, 74, 242))
                    sub = self.cfg['common'].upper()
                    p.drawText(QPointF(cx0-p.fontMetrics().horizontalAdvance(sub)/2, ly+20), sub)
                    p.setOpacity(1)
                if not self.sparks and tn-self.complete_at > 0.2:
                    for s in fig:
                        for _ in range(2):
                            self.sparks.append({'x': s['_x']+(random.random()-.5)*8, 'y': s['_y'],
                                                'vx': (random.random()-.5)*14, 'vy': -14-random.random()*22,
                                                'born': tn+random.random()*0.8})
            if self.cfg.get('explore') or self.cfg.get('tour'):
                la = 0.8
                if self.cfg.get('tour'): la = clamp((52-self.cam['view'])/22, 0, 1)*0.85
                if la > 0.02:
                    for s in fig:
                        if -40 < s['_x'] < self.W+40 and -30 < s['_y'] < self.H+30:
                            self.draw_label(p, s, la)
                if self.cfg.get('tour') and self.cam['view'] < 15:
                    for s in self.named:
                        if not s.get('figure') and -40 < s['_x'] < self.W+40 and -30 < s['_y'] < self.H+30:
                            self.draw_label(p, s, 0.5)
            self.sparks = [q for q in self.sparks if tn-q['born'] < 1.5]
            for q in self.sparks:
                if tn < q['born']: continue
                k = (tn-q['born'])/1.5
                q['x'] += q['vx']*0.033; q['y'] += q['vy']*0.033; q['vy'] -= 0.2
                p.setPen(Qt.NoPen); p.setBrush(QColor(232, 200, 119, int((1-k)*178)))
                p.drawEllipse(QPointF(q['x'], q['y']), 1.1, 1.1)
        p.restore()

    def draw_label(self, p, s, a):
        dx = s['_x']-self.cx0; dy = s['_y']-self.cy0
        L = math.hypot(dx, dy) or 1; dx /= L; dy /= L
        lx = s['_x']+dx*(s['_r']+9); ly = s['_y']+dy*(s['_r']+9)
        f = QFont(); f.setFamilies(['Fraunces', 'Georgia', 'serif'])
        f.setItalic(True); f.setWeight(QFont.Light); f.setPixelSize(13)
        p.setFont(f); p.setOpacity(a); p.setPen(QColor(233, 224, 199))
        fm = p.fontMetrics(); tw = fm.horizontalAdvance(s['name']); th = fm.height()
        ax = lx-tw/2 if abs(dx) <= 0.3 else (lx if dx > 0.3 else lx-tw)
        ay = ly+th/3 if abs(dy) <= 0.3 else (ly if dy > 0.3 else ly+th*0.8)
        p.drawText(QPointF(ax, ay), s['name']); p.setOpacity(1)

    def draw_grid(self, p):
        p.save(); p.setPen(Qt.NoPen)
        topD = self.cam['dec']+(self.H/2)/self.ppd; botD = self.cam['dec']-(self.H/2)/self.ppd
        d = math.ceil(botD/10)*10
        while d <= topD:
            if abs(d) < 90:
                y = self.H/2-(d-self.cam['dec'])*self.ppd
                p.setPen(QPen(QColor(201, 162, 74, 56 if d == 0 else 20), 1))
                p.drawLine(0, int(y), self.W, int(y))
            d += 10
        cosd = max(0.15, math.cos(self.cam['dec']*DEG))
        lftH = self.cam['ra']-(self.W/2)/(15*cosd*self.ppd)
        rgtH = self.cam['ra']+(self.W/2)/(15*cosd*self.ppd)
        f = QFont(); f.setFamilies(['IBM Plex Mono', 'Consolas', 'monospace']); f.setPixelSize(9)
        p.setFont(f)
        h = math.ceil(lftH/2)*2
        while h <= rgtH:
            x = self.proj(h, self.cam['dec'])[0]
            p.setPen(QPen(QColor(201, 162, 74, 20), 1)); p.drawLine(int(x), 0, int(x), self.H)
            p.setPen(QColor(201, 162, 74, 102))
            p.drawText(QPointF(x-8, self.H-8), '%dʰ' % int(mod24(h)))
            h += 2
        ey = self.H/2+self.cam['dec']*self.ppd
        if 14 < ey < self.H-14:
            p.setPen(QColor(201, 162, 74, 115)); p.drawText(QPointF(10, ey-5), 'celestial equator')
        p.setPen(QPen(QColor(224, 122, 63, 102), 1, Qt.DashLine))
        path = QPainterPath(); started = False
        hh = lftH
        while hh <= rgtH+0.05:
            dec = math.asin(0.3978*math.sin(hh*15*DEG))/DEG
            x, y = self.proj(hh, dec)
            if not started: path.moveTo(x, y); started = True
            else: path.lineTo(x, y)
            hh += 0.06
        p.drawPath(path); p.setPen(QColor(224, 122, 63, 140))
        x, y = self.proj(6, 23.44)
        if -40 < x < self.W+40 and 0 < y < self.H: p.drawText(QPointF(x, y+16), 'ecliptic')
        p.restore()

# ============================== HTML helpers ==============================
def page(body):
    return ('<div style="font-size:13.5px;line-height:1.6;">' + body + '</div>')
def over(t): return ('<div style="font-family:\'IBM Plex Mono\',Consolas,monospace;font-size:10px;'
                     'letter-spacing:3px;color:#C9A24A;text-transform:uppercase;">%s</div>' % t)
def h1(t, sm=False):
    return ('<div style="font-family:Fraunces,Georgia,serif;font-weight:400;%s;font-size:%dpx;'
            'margin:8px 0 2px;color:#EFE7CF;"><i>%s</i></div>' %
            ('' if not sm else '', 36 if not sm else 26, t))
def sub(t): return ('<div style="font-family:\'IBM Plex Mono\',Consolas,monospace;font-size:10.5px;'
                    'letter-spacing:2px;color:rgba(231,221,196,.62);text-transform:uppercase;">%s</div>' % t)
def tale_p(t):
    return ('<p style="font-style:italic;font-weight:300;font-size:15px;line-height:1.7;'
            'color:rgba(231,221,196,.85);white-space:pre-line;">%s</p>' % t)
def fact_html(f, i):
    icons = ['✦', '🔭', '⊕', '🌐', '📖']
    t = f['t'] if isinstance(f, dict) else f
    at = ''
    if isinstance(f, dict) and 'at' in f:
        ra, dec, v = f['at']
        at = ('<br><a style="color:#C9A24A;font-size:10px;letter-spacing:2px;" href="seek:%s,%s,%s">'
              'find it · fly there</a>' % (ra, dec, v))
    return ('<div style="display:flex;gap:10px;margin:11px 0;color:rgba(231,221,196,.85);">'
            '<span style="color:#C9A24A;">%s</span><span>%s%s</span></div>' % (icons[i % 5], t, at))
def mons_line(lv):
    return 'best at midnight: <b style="color:#C9A24A;">%s</b>' % (month_label(lv['months']) or '—')

# ============================== dialogs ==============================
class PanelDialog(QDialog):
    def __init__(self, main, title=''):
        super().__init__(main)
        self.main = main
        self.setWindowTitle(title)
        self.setModal(True)
        self.resize(660, 640)
        self.v = QVBoxLayout(self); self.v.setContentsMargins(34, 28, 34, 26)
        self.body = QTextBrowser(); self.body.setOpenExternalLinks(False)
        self.body.setFrameShape(QFrame.NoFrame)
        self.body.anchorClicked.connect(self.main.handle_link)
        self.v.addWidget(self.body, 1)
        self.btns = QHBoxLayout(); self.btns.addStretch(1)
        self.v.addLayout(self.btns)
    def add_btn(self, text, fn, primary=False):
        b = QPushButton(text)
        if primary: b.setObjectName('primary')
        b.clicked.connect(fn); self.btns.addWidget(b); return b

class PlateDialog(PanelDialog):
    def __init__(self, main, lv):
        super().__init__(main, 'Asterisma — Plate %s' % lv['numeral'])
        notes = ''.join('<div style="display:flex;gap:9px;margin:9px 0;color:rgba(231,221,196,.75);">'
                        '<span style="color:#C9A24A;">✦</span><span>%s</span></div>' % n for n in lv['notes'])
        self.body.setHtml(page(
            over('Plate %s of %s' % (lv['numeral'], rom(len(LEVELS)))) +
            h1('%s' % lv['name']) + sub('%s · seen from %s' % (lv['common'], lv['frm'])) +
            '<div style="display:grid;grid-template-columns:1.2fr 1fr;gap:26px;">'
            '<div><hr style="border:none;border-top:1px solid rgba(201,162,74,26%);">' +
            tale_p(lv['tale']) + '</div><div>' + notes +
            '<div style="font-size:11px;color:rgba(231,221,196,.45);margin-top:12px;">' + mons_line(lv) +
            '<br>%d lines · %d embers · a false line burns one</div></div></div>' %
            (len(lv['edges']), lv['embers']) +
            '<div style="font-size:9.5px;color:rgba(231,221,196,.4);margin-top:14px;">'
            'Star places are true (J2000), lightly spaced for legibility. Drag to pan · scroll to zoom.</div>'))
        self.add_btn('Chart the figure', self.main.begin_charting, primary=True)

class StudyDialog(PanelDialog):
    def __init__(self, main, lv, explore, starsN=3):
        super().__init__(main, 'Asterisma — %s' % lv['name'])
        self.lv = lv
        verdict = ('A study chart. Pan, zoom, hover — the sky keeps its stories.' if explore else
                   ['','Charted, after some wandering.','Charted — one or two false lines.',
                    'Flawless — not one false line.'][starsN])
        best = main.save['best'].get(lv['id'])
        if best and not explore: verdict += ' · best %s' % fmtT(best)
        rows = ''.join('<tr><td>%s</td><td class=m>%s</td><td class=m>%.2f</td>'
                       '<td class=m><span style="color:%s">●</span> %s</td><td class=m>%s</td></tr>'
                       % (s['name'], s['bayer'], s['mag'], SPEC[s['cls']], s['spec'], s['dist'])
                       for s in lv['stars'] if s['figure'])
        facts = ''.join(fact_html(f, i) for i, f in enumerate(lv['facts']))
        cults = ''.join('<div style="border-left:2px solid rgba(201,162,74,50%);padding-left:13px;margin:14px 0;">'
                        '<div style="font-family:\'IBM Plex Mono\',monospace;font-size:9px;letter-spacing:3px;'
                        'color:#C9A24A;text-transform:uppercase;">%s</div>'
                        '<div style="font-style:italic;font-size:16px;margin:3px 0 4px;">%s</div>'
                        '<div style="color:rgba(231,221,196,.85);line-height:1.6;">%s</div></div>' % c
                        for c in lv['cultures'])
        idx = next(i for i, x in enumerate(LEVELS) if x['id'] == lv['id'])
        dark_chip = ('<div style="font-size:10px;letter-spacing:2px;color:rgba(231,221,196,.6);">☾ '
                     'charted by dark alone</div>'
                     if (not explore and main.save['done'].get(lv['id'], {}).get('dark')) else '')
        acts = '<div style="margin-top:20px;display:flex;gap:10px;justify-content:flex-end;flex-wrap:wrap;">'
        if lv['id'] in ('uma', 'cassiopeia', 'crux'):
            acts += '<a class="btnlink" href="wheel:%s">Watch it wheel</a> ' % lv['id']
        acts += '<a class="btnlink" href="study:%d">Study this sky</a> ' % idx
        if idx < len(LEVELS)-1:
            acts += '<a class="btnlink primary" href="next:%d">Next plate — %s</a>' % (idx+1, LEVELS[idx+1]['name'])
        else:
            acts += '<a class="btnlink primary" href="finish:1">The finished atlas</a>'
        acts += '</div>'
        self.body.setHtml(page(
            over('Plate %s — %s' % (lv['numeral'], 'study chart' if explore else 'charted')) +
            h1(lv['name']) + sub('%s · %s' % (lv['common'], lv['frm'])) +
            '<div style="font-size:11px;color:rgba(231,221,196,.45);margin:8px 0;">' + mons_line(lv) + '</div>' +
            ('<div style="color:#E8C877;">★%s</div>' % ('★' * starsN if False else '·' * starsN) if not explore else '') +
            '<div style="font-style:italic;color:rgba(231,221,196,.62);font-size:13px;">' + verdict + '</div>' + dark_chip +
            '<div style="font-family:\'IBM Plex Mono\',monospace;font-size:10px;letter-spacing:3px;color:#C9A24A;'
            'margin:22px 0 8px;padding-top:16px;border-top:1px solid rgba(201,162,74,26%);">THE STARS OF THE FIGURE</div>' +
            '<table width="100%%" style="font-size:11px;border-collapse:collapse;">'
            '<tr><th align=left style="color:rgba(231,221,196,.4);font-weight:400;">Star</th>'
            '<th align=left>Desig.</th><th align=left>Mag</th><th align=left>Type</th><th align=left>Dist</th></tr>'
            + rows + '</table>' +
            '<div style="font-family:\'IBM Plex Mono\',monospace;font-size:10px;letter-spacing:3px;color:#C9A24A;'
            'margin:22px 0 8px;padding-top:16px;border-top:1px solid rgba(201,162,74,26%);">THE SKY</div>' + facts +
            '<div style="font-family:\'IBM Plex Mono\',monospace;font-size:10px;letter-spacing:3px;color:#C9A24A;'
            'margin:22px 0 8px;padding-top:16px;border-top:1px solid rgba(201,162,74,26%);">THE STORIES</div>' + cults +
            acts))
        self.add_btn('Back to the sky', self.close)

class HelpDialog(PanelDialog):
    def __init__(self, main):
        super().__init__(main, 'Asterisma — how to chart')
        steps = [('✦', 'Find the ember-light',
                  'Stars that belong to the figure breathe with a faint warm halo — the atlas’s gift, not the sky’s. '
                  'In dark-sky mode the halo dims, and so does the interface.'),
                 ('⊕', 'Draw line by line',
                  'Click one star, then a second. A true line holds in silver; a false line burns an ember. '
                  'With a star chosen, the status bar reads its separation and altitude.'),
                 ('⌕', 'Summon by name',
                  'Press / and type — Vega, M31, Jupiter. The finder flies the instrument there and readies the star.'),
                 ('🏙', 'Choose your sky',
                  'Press Q to cycle sky quality from a Bortle 1 desert to a downtown glow. '
                  'Watch the Milky Way drown and the faint stars vanish — then find them again.'),
                 ('⌖', 'Step outside',
                  'Tonight’s Sky takes your latitude and tells you which plates are up, how high, and when '
                  'each crosses the meridian — plus the Moon’s phase and the five naked-eye planets.'),
                 ('🔭', 'Watch for faint pulses',
                  'Breathing circles mark hidden things — nebulae, clusters, the ghosts of dead stars. '
                  'The Bear, the Queen and the Cross offer a wheel-viewer of the circumpolar dance.')]
        body = over('how to chart') + h1('Three habits of the old navigators', sm=True) + \
               '<hr style="border:none;border-top:1px solid rgba(201,162,74,26%);">'
        for ic, t, d in steps:
            body += ('<div style="display:flex;gap:13px;margin:15px 0;"><span style="color:#C9A24A;">%s</span>'
                     '<div><b style="font-style:italic;font-family:Fraunces,Georgia,serif;">%s</b>'
                     '<div style="color:rgba(231,221,196,.75);font-size:13.5px;line-height:1.55;">%s</div></div></div>'
                     % (ic, t, d))
        body += ('<div class=m style="font-size:10px;color:rgba(231,221,196,.45);line-height:2;">'
                 '<kbd>/</kbd> finder · <kbd>Q</kbd> sky quality · <kbd>?</kbd> help · <kbd>T</kbd> tonight · '
                 '<kbd>N</kbd> next figure star · <kbd>Enter</kbd> pick · arrows pan · <kbd>+</kbd>/<kbd>−</kbd> zoom · '
                 '<kbd>0</kbd> reset · <kbd>G</kbd> grid · <kbd>D</kbd> dark sky</div>'
                 '<div style="margin-top:10px;">' +
                 ' '.join('<span style="font-family:\'IBM Plex Mono\',monospace;font-size:10px;color:rgba(231,221,196,.6);">'
                          '<span style="color:%s">●</span>%s&nbsp;&nbsp;</span>' % (c, k)
                          for k, c in SPEC.items()) +
                 '<div style="font-size:9.5px;color:rgba(231,221,196,.4);margin-top:6px;">'
                 'O ≥ 30,000 K · B ≈ 20,000 · A ≈ 9,000 · F ≈ 7,000 · G ≈ 5,600 · K ≈ 4,400 · M ≤ 3,700 K — '
                 'blue burns hotter than red, whatever the size.</div></div>')
        self.body.setHtml(page(body))
        self.add_btn('Back', self.close)

class AtlasDialog(PanelDialog):
    def __init__(self, main):
        super().__init__(main, 'Asterisma — plate index')
        rows = ''
        for i, lv in enumerate(LEVELS):
            d = main.save['done'].get(lv['id'])
            best = main.save['best'].get(lv['id'])
            tail = (' · best %s' % fmtT(best)) if best and d else ''
            stars = ('<span style="color:#E8C877;">%s</span>' % ('★'*d['stars'] + '·'*(3-d['stars']))) if d else \
                    ('<span style="color:rgba(231,221,196,.35);font-size:10px;">unplotted</span>' if main.unlocked(i) else '')
            if main.unlocked(i):
                rows += ('<a class="rowlink" href="goto:%d"><b style="color:#C9A24A;font-style:italic;">%s</b>'
                         '&nbsp;&nbsp;%s <i style="color:rgba(231,221,196,.55);font-size:12px;">%s%s</i>'
                         '&nbsp;&nbsp;%s</a>' % (i, lv['numeral'], lv['name'], lv['common'], tail, stars))
                if d:
                    rows += '&nbsp;<a class="btnlink" href="study:%d" style="font-size:9px;">study</a>' % i
            else:
                rows += ('<span style="opacity:.4;"><b style="color:#C9A24A;font-style:italic;">%s</b>'
                         '&nbsp;&nbsp;%s <i>%s</i> 🔒</span>' % (lv['numeral'], lv['name'], lv['common']))
            rows += '<div style="border-bottom:1px solid rgba(201,162,74,14%);margin:4px 0;"></div>'
        extra = ''
        if all(lv['id'] in main.save['done'] for lv in LEVELS):
            extra = ('<div style="margin-top:16px;text-align:right;">'
                     '<a class="btnlink primary" href="tour:1">Walk the whole vault</a></div>')
        self.body.setHtml(page(over('plate index') + h1('The atlas so far', sm=True) +
                               '<hr style="border:none;border-top:1px solid rgba(201,162,74,26%);">' + rows +
                               '<div style="font-size:9.5px;color:rgba(231,221,196,.4);margin-top:12px;">'
                               'Progress is kept in ~/.asterisma.json.</div>' + extra))
        self.add_btn('Close', self.close)

class ChronicleDialog(PanelDialog):
    ENTRIES = [
     ('c. 1600 BCE','The Nebra Sky Disc','A bronze disc buried in what is now Germany shows a crescent, a full moon, and a cluster of seven — likely the Pleiades, whose dawn rising marked the year. The oldest concrete sky-map we have.',5),
     ('c. 700 BCE','Farming by the stars','“When the Pleiades rise, it is time to use the sickle,” wrote Hesiod — Greek farmers kept their calendar in the sky, as the Chinese Book of Odes kept theirs.',5),
     ('36 CE','A hundred meteors','Chinese chronicles record “more than a hundred meteors” streaming from a point in the north-east — the earliest known observation of the Perseids.',10),
     ('130 CE','Ptolemy writes the catalogue','The Almagest fixes 1,022 stars and 48 constellations — the atlas Europe would follow for 1,400 years. Ptolemy also records M7 on the Scorpion’s tail.',9),
     ('964 CE','al-Ṣūfī’s Book of Fixed Stars','In Isfahan, al-Ṣūfī redraws the heavens and records “a little cloud” beside the chained princess — the first note of a galaxy beyond our own.',4),
     ('1054 CE','A guest star','Chinese astronomers log a “guest star” bright enough for daylight for 23 days. Its remnant is the Crab Nebula.',5),
     ('1572','Tycho’s star','A new star over Denmark shakes the “unchanging heavens”. Tycho Brahe measures it far beyond the Moon: the sky itself can change.',3),
     ('1610','Galileo points a spyglass','The Milky Way “is nothing else but a mass of innumerable stars planted together in clusters”.',0),
     ('1650','Mizar comes apart','Riccioli finds two stars where the eye saw one: the first telescopic double. Mizar is really four suns.',6),
     ('1838','Bessel measures the abyss','Bessel detects the annual wobble of 61 Cygni: the first stellar parallax. The universe becomes terrifyingly large.',None),
     ('1862','The companion of Sirius','Alvan Clark finds Sirius B — Earth-sized with the Sun’s mass: the first white dwarf. A teaspoonful would weigh tonnes.',8),
     ('1924','Island universes','Hubble finds Cepheids in Andromeda’s “little cloud”: it lies millions of light-years off.',4),
     ('1930s','The sky begins to leak away','Cities wire themselves with electric light, and the stars start to vanish for the people below.',10),
     ('1971','The first black hole','X-rays from the neck of the Swan betray an invisible mass of some fifteen Suns: Cygnus X-1.',0),
     ('1973','The missing light','Rubin and Ford measure how M31 spins: dark matter stops being a curiosity and becomes a problem.',4),
     ('2019–20','Betelgeuse dims','The red shoulder of Orion fades to a third of its light. It was dust — but one day it will truly detonate.',7),
     ('2022','Matariki, a holiday','Aotearoa New Zealand makes the rising of the Pleiades an official public holiday.',5)]
    def __init__(self, main):
        super().__init__(main, 'Asterisma — chronicle')
        body = over('the chronicle') + h1('%d moments in the long look upward' % len(self.ENTRIES), sm=True) + \
               '<hr style="border:none;border-top:1px solid rgba(201,162,74,26%);"><div style="margin-left:6px;">'
        for y, t, x, go in self.ENTRIES:
            link = ''
            if go is not None and main.unlocked(go):
                link = '<br><a style="color:#C9A24A;font-size:10px;letter-spacing:2px;" href="chgo:%d">visit the plate · %s</a>' % (go, LEVELS[go]['name'])
            body += ('<div style="border-left:1px solid rgba(201,162,74,26%);padding:0 0 14px 18px;position:relative;">'
                     '<div style="font-family:\'IBM Plex Mono\',monospace;font-size:10px;letter-spacing:2px;color:#C9A24A;">%s</div>'
                     '<div style="font-style:italic;font-size:16px;margin:2px 0 3px;">%s</div>'
                     '<div style="color:rgba(231,221,196,.75);font-size:13.5px;line-height:1.55;">%s</div>%s</div>'
                     % (y, t, x, link))
        self.body.setHtml(page(body + '</div>'))
        self.add_btn('Back', self.close)

class TonightDialog(PanelDialog):
    def __init__(self, main):
        super().__init__(main, 'Asterisma — tonight’s sky')
        self.setMinimumSize(640, 700)
        top = QHBoxLayout()
        self.lat = QLineEdit(); self.lon = QLineEdit()
        geo = main.save.get('geo') or {'lat': 45.0, 'lon': 0.0}
        self.lat.setText('%.1f' % geo['lat']); self.lon.setText('%.1f' % geo['lon'])
        self.lat.setFixedWidth(90); self.lon.setFixedWidth(90)
        for lab, w in (('latitude', self.lat), ('longitude', self.lon)):
            top.addWidget(QLabel(lab)); top.addWidget(w)
        b1 = QPushButton('set'); b2 = QPushButton('use my location')
        b1.clicked.connect(self.set_geo); b2.clicked.connect(self.use_geo)
        top.addWidget(b1); top.addWidget(b2); top.addStretch(1)
        self.v.insertLayout(0, top)
        self.refresh()
    def set_geo(self):
        try:
            la = clamp(float(self.lat.text()), -89.5, 89.5)
            lo = clamp(float(self.lon.text()), -180, 180)
        except ValueError:
            self.main.toast('A latitude between −90 and 90, a longitude between −180 and 180.'); return
        self.main.save['geo'] = {'lat': la, 'lon': lo}; persist(self.main.save)
        self.main.grant('skywise'); self.refresh()
    def use_geo(self):
        from PySide6.QtPositioning import QGeoPositionInfoSource
        src = QGeoPositionInfoSource.createDefaultSource(self)
        if src is None:
            self.main.toast('No position fixes here — enter a latitude by hand.'); return
        self.main.toast('Asking the device where on Earth it is…')
        src.positionUpdated.connect(self._got); src.startUpdates()
        QTimer.singleShot(8000, src.stopUpdates)
    def _got(self, info):
        c = info.coordinate()
        self.main.save['geo'] = {'lat': c.latitude(), 'lon': c.longitude()}
        persist(self.main.save); self.main.grant('skywise'); self.refresh()
    def refresh(self):
        build_wanderers()
        geo = self.main.save.get('geo') or {'lat': 45, 'lon': 0}
        ast = astro()
        lst = (ast[1] + geo['lon'] + 360) % 360
        tstr = time.strftime('%H:%M')
        m = wanderers[0]
        mA = alt_of(geo['lat'], geo['lon'], m['raH']*15, m['dec'], ast)
        advice = ('A bright Moon — favour the bright figures.' if m['illum'] > 0.66 else
                  'A moonless night — the faint things are yours.' if m['illum'] < 0.12 else
                  'Moderate moonlight — faint objects remain within reach.')
        moon_html = ('<div style="display:flex;gap:14px;align-items:center;padding:10px 0;'
                     'border-bottom:1px solid rgba(201,162,74,14%);">'
                     '<img src="moonpix" width="52" height="52">'
                     '<div><b style="font-style:italic;font-size:16px;">%s · %d%% lit</b><br>'
                     '<span style="font-family:\'IBM Plex Mono\',monospace;font-size:10.5px;color:rgba(231,221,196,.62);">%s%s · %s km</span><br>'
                     '<i style="font-size:12.5px;color:rgba(231,221,196,.75);">%s</i></div></div>'
                     % (m['phaseName'], round(m['illum']*100), sky_status(mA),
                        (' · toward '+cardinal(mA['az'])) if mA['alt'] > 0 else '',
                        format(round(m['distKm']), ','), advice))
        prow = ''
        for w in wanderers[1:]:
            a = alt_of(geo['lat'], geo['lon'], w['raH']*15, w['dec'], ast)
            where = ('%d° up · toward %s' % (round(a['alt']), cardinal(a['az']))) if a['alt'] > -2 else 'below the horizon'
            prow += ('<div style="padding:8px 0;border-bottom:1px solid rgba(201,162,74,14%);%s">'
                     '<span style="color:%s">●</span> <b>%s</b>%s<br>'
                     '<span style="font-family:\'IBM Plex Mono\',monospace;font-size:10.5px;color:rgba(231,221,196,.62);">'
                     '≈ mag %.1f · %.2f AU · %s</span></div>'
                     % ('opacity:.5;' if a['alt'] <= -2 else '', w['col'], w['name'],
                        ' <i style="font-size:11px;">· lost in the Sun’s glare</i>' if w['glare'] else '',
                        w['mag'], w['au'], where))
        rows = sorted(((alt_of(geo['lat'], geo['lon'], lv['center'][0]*15, lv['center'][1], ast), lv, i)
                       for i, lv in enumerate(LEVELS)), key=lambda r: -r[0]['alt'])
        upN = sum(1 for r in rows if r[0]['alt'] > 0)
        lst_html = ''
        for a, lv, i in rows:
            tr = 'on the meridian now' if a['transit'] == 0 else 'meridian in '+fmtH(a['transit'])
            bits = ' · '.join(x for x in [sky_status(a), 'circumpolar' if a['always'] else '', tr,
                                          cardinal(a['az']) if a['alt'] > 0 else ''] if x)
            if main.unlocked(i):
                act = '<a class="btnlink" href="goto:%d">chart it</a>' % i
            else:
                act = '<span style="font-family:\'IBM Plex Mono\',monospace;font-size:9px;color:rgba(231,221,196,.35);">LOCKED</span>'
            lst_html += ('<div style="padding:9px 0;border-bottom:1px solid rgba(201,162,74,14%);%s">'
                         '<table width="100%%"><tr><td><b>%s</b> <i style="font-size:12px;color:rgba(231,221,196,.6);">%s</i>'
                         '<div style="height:4px;background:rgba(201,162,74,12%);width:300px;margin:5px 0 3px;">'
                         '<div style="height:4px;width:%d%%;background:linear-gradient(90deg,rgba(201,162,74,45%%),#E8C877);"></div></div>'
                         '<span style="font-family:\'IBM Plex Mono\',monospace;font-size:10px;color:rgba(231,221,196,.62);">%s</span>'
                         '</td><td align=right valign=middle>%s</td></tr></table></div>'
                         % ('opacity:.5;' if a['alt'] <= 0 else '', lv['name'], lv['common'],
                            clamp(a['alt'], 0, 90)/90*100, bits, act))
        self.body.setHtml(page(
            over('tonight’s sky') + h1('What the hours hold', sm=True) +
            sub('%.1f° %s · %.1f° %s · local %s · LST %s' %
                (abs(geo['lat']), 'N' if geo['lat'] >= 0 else 'S', abs(geo['lon']),
                 'E' if geo['lon'] >= 0 else 'W', tstr, fmtRA(lst/15))) +
            '<hr style="border:none;border-top:1px solid rgba(201,162,74,26%);">' +
            moon_html + sub('the wandering planets') + prow +
            sub('%d of %d figures above your horizon right now' % (upN, len(LEVELS))) + lst_html +
            '<div style="font-size:9.5px;color:rgba(231,221,196,.4);margin-top:12px;">Computed in this process with '
            'sidereal time and the spherical triangle; the Moon and planets from simplified Keplerian elements, good to '
            'a degree or two. Your latitude never leaves the machine.</div>'))
        self.body.document().addResource(QImage.ProviderTypeInvalid if False else 2, QUrl('moonpix'), self._moon_pix())
        self.body.setHtml(self.body.toHtml())
    def _moon_pix(self):
        m = wanderers[0]
        pm = QPixmap(104, 104); pm.fill(Qt.transparent)
        p = QPainter(pm); p.setRenderHint(QPainter.Antialiasing)
        draw_moon_disc(p, 52, 52, 40, m['illum'], m['waxing'], True); p.end()
        return pm
    def add_btn(self, *a, **k): pass  # tonight dialog keeps its own action row

class FinderDialog(QDialog):
    def __init__(self, main):
        super().__init__(main)
        self.main = main
        self.setWindowTitle('Asterisma — the finder')
        self.setModal(True); self.resize(480, 480)
        v = QVBoxLayout(self)
        lab = QLabel('Summon anything in this sky')
        lab.setStyleSheet('font-family:Fraunces,Georgia,serif;font-size:24px;')
        v.addWidget(lab)
        self.inp = QLineEdit(); self.inp.setPlaceholderText('a star, a planet, a hidden cloud, a plate…')
        self.inp.textChanged.connect(self.render)
        self.inp.returnPressed.connect(self.pick)
        v.addWidget(self.inp)
        self.lst = QListWidget(); self.lst.itemActivated.connect(lambda _: self.pick())
        self.lst.currentRowChanged.connect(lambda r: setattr(self, 'sel', r))
        v.addWidget(self.lst, 1)
        hint = QLabel('↑↓ to move · Enter to summon · Esc to close')
        hint.setStyleSheet('font-family:\'IBM Plex Mono\',monospace;font-size:9.5px;color:rgba(231,221,196,.4);')
        v.addWidget(hint)
        self.sel = 0; self.items = []; self.view = []
        self.build_items(); self.render('')
        self.inp.setFocus()
    def keyPressEvent(self, ev):
        if ev.key() == Qt.Key_Down:
            self.sel = min(self.sel+1, len(self.view)-1); self.render(self.inp.text()); return
        if ev.key() == Qt.Key_Up:
            self.sel = max(self.sel-1, 0); self.render(self.inp.text()); return
        super().keyPressEvent(ev)
    def build_items(self):
        main = self.main; self.items = []
        sv = main.sky
        if main.scene == 'game':
            for s in sv.named:
                self.items.append(('star', s['name'], '%s · mag %.2f' % (s['bayer'], s['mag']), s))
            for f in sv.fuzzies:
                self.items.append(('hidden', f['name'], 'a hidden object', f))
            for w in wanderers:
                sub = ('%s · %d%% lit' % (w['phaseName'], round(w['illum']*100))) if w['kind'] == 'moon' \
                      else 'a wandering planet'
                self.items.append((w['kind'], w['name'], sub, w))
        else:
            for i, lv in enumerate(LEVELS):
                self.items.append(('plate', lv['name'], 'Plate %s · %s' % (lv['numeral'], lv['common']), i))
        self.items.sort(key=lambda it: it[1])
    def render(self, q):
        q = (q or '').strip().lower()
        self.view = [it for it in self.items if not q or q in it[1].lower() or q in it[2].lower()][:14]
        self.sel = clamp(self.sel, 0, max(0, len(self.view)-1))
        self.lst.clear()
        for i, it in enumerate(self.view):
            it2 = QListWidgetItem('%s   —   %s' % (it[1], it[2]))
            if i == self.sel:
                it2.setForeground(QColor('#E8C877'))
            self.lst.addItem(it2)
        if self.view and 0 <= self.sel < self.lst.count():
            self.lst.setCurrentRow(self.sel)
    def pick(self):
        if not self.view: return
        it = self.view[self.sel]; main = self.main
        if it[0] == 'plate':
            if main.unlocked(it[3]): self.close(); main.load_level(it[3])
            return
        self.close(); main.grant('finder')
        sv = main.sky
        if it[0] == 'star':
            sv.fly_to(it[3]['ra'], it[3]['dec'], min(sv.cam['view'], main.sky.cfg['view']))
            if main.scene == 'game' and main.sky.phase == 'playing' and not sv.cfg.get('tour') and not sv.cfg.get('explore'):
                sv.select_star(it[3])
            else:
                sv.focus_star = it[3]
        elif it[0] == 'hidden':
            sv.fly_to(it[3]['ra'], it[3]['dec'])
            main.toast(it[3]['name']+' — hover the pulse when you arrive.')
        else:
            sv.fly_to(it[3]['raH'], it[3]['dec'])
            main.toast('The Moon, where it stands tonight.' if it[0] == 'moon'
                       else 'A wanderer — the word means “going astray”.')

class TrialDialog(QDialog):
    CURATED = [
     ('What is the middle “star” of Orion’s sword?',['The Orion Nebula — a star nursery','A black hole','The planet Jupiter','An optical illusion'],0),
     ('Merak and Dubhe, the Dipper’s pointers, are useful because…',['Their line aims at Polaris','They never twinkle','They are the closest stars','They mark the ecliptic'],0),
     ('Why will the pole star change over the ages?',['Earth’s axis slowly wobbles (precession)','Polaris is burning out','The constellations drift apart','The Sun is losing mass'],0),
     ('Which of these stars lies closest to Earth?',['Sirius','Deneb','Antares','Albireo'],0),
     ('The Great Rift splitting the Milky Way is…',['A lane of cold dust','A river of dark matter','A gap between galaxies','The Moon’s shadow'],0),
     ('“Follow the Drinking Gourd” was…',['A star map to freedom north','A sailor’s shanty about rum','A Greek myth of Dionysus','A Chinese harvest song'],0),
     ('The pre-dawn rising of Matariki marks…',['The Māori new year','The solstice in Egypt','Orion’s return','A solar eclipse'],0),
     ('A red star’s colour tells you it is…',['Comparatively cool','Filled with iron','The youngest of its cluster','About to vanish'],0),
     ('The Nebra Sky Disc, ~3,600 years old, may show…',['The Pleiades','Orion’s Belt','The Southern Cross','Ursa Minor'],0),
     ('Antares will end its life as…',['A daytime supernova','A slow fade to black','A white dwarf at once','A comet'],0),
     ('Tycho’s Star of 1572 proved that…',['The heavens can change','Planets have moons','Light has a speed','Comets return'],0),
     ('Albireo, through a small telescope, shows…',['One gold and one blue star','A ring of gas','Eight flashing points','A black disk'],0),
     ('Sirius appears brightest of all night stars mainly because it is…',['Modest in output but very near','The largest star known','The hottest star known','At the centre of the galaxy'],0),
     ('Sothis’s dawn rising told the Egyptians that…',['The Nile would soon flood','It was time to harvest grapes','An eclipse was coming','Winter had begun'],0),
     ('A star is circumpolar when…',['Its whole circle around the pole stays above your horizon','It is brighter than magnitude 0','It lies on the ecliptic','It never leaves the zodiac'],0),
     ('The farthest thing most eyes can see unaided is…',['The Andromeda Galaxy','Saturn','The Orion Nebula','The Coalsack'],0),
     ('Algol, the “winking demon”, dims because…',['A companion star regularly eclipses it','It passes behind the Moon each month','Dust clouds cross its face yearly','It rotates fast enough to dim'],0),
     ('The August Perseids are dust from…',['Comet Swift–Tuttle','Comet Halley','Asteroid Vesta','The planet Mercury'],0),
     ('From a Bortle 9 downtown sky, what mostly disappears?',['The Milky Way and every faint star','The Moon and planets','Orion’s Belt','All stars without exception'],0)]
    def __init__(self, main):
        super().__init__(main)
        self.main = main; self.setWindowTitle('The Navigator’s Trial'); self.setModal(True)
        self.resize(620, 420)
        self.v = QVBoxLayout(self); self.v.setContentsMargins(34, 28, 34, 26)
        self.qs = self.make_pool()[:8]
        random.shuffle(self.qs); self.qs = self.qs[:8]
        self.i = 0; self.score = 0
        self.show_q()
    def make_pool(self):
        P = []
        ls = LEVELS[:]; random.shuffle(ls)
        for lv in ls[:6]:
            figs = [s for s in lv['stars'] if s['figure']]
            best = min(figs, key=lambda s: s['mag'])
            decoys = []
            for x in LEVELS:
                if x is lv: continue
                decoys += [s['name'] for s in x['stars'] if s['figure'] and s['name'] != best['name']]
            random.shuffle(decoys)
            opts = [best['name']] + decoys[:3]; random.shuffle(opts)
            P.append(('Which of these is the brightest star of %s?' % lv['name'], opts, opts.index(best['name'])))
        for lv in random.sample(LEVELS, 4):
            c = random.choice(lv['cultures'])
            names = [x['name'] for x in LEVELS if x is not lv]
            random.shuffle(names)
            opts = [lv['name']] + names[:3]; random.shuffle(opts)
            P.append(('The tale “%s” is told about which sky?' % c[1], opts, opts.index(lv['name'])))
        classes = 'OBAFGKM'
        for _ in range(2):
            pool = [s for lv in LEVELS for s in lv['stars']]
            random.shuffle(pool); picks = []
            for s in pool:
                if len(picks) < 4 and s['cls'] not in [p['cls'] for p in picks]: picks.append(s)
            if len(picks) == 4:
                picks.sort(key=lambda s: classes.index(s['cls']))
                names = [s['name'] for s in picks]
                hot = names[0]; rest = names[1:]; random.shuffle(rest)
                opts = [hot]+rest
                P.append(('Which of these stars burns hottest?', opts, 0))
        for q, o, a in self.CURATED:
            o2 = o[:]; correct = o2[a]; random.shuffle(o2)
            P.append((q, o2, o2.index(correct)))
        seen = set(); out = []
        for x in P:
            if x[0] not in seen: seen.add(x[0]); out.append(x)
        return out
    def show_q(self):
        while self.v.count():
            it = self.v.takeAt(0); w = it.widget()
            if w: w.deleteLater()
        q, opts, _ = self.qs[self.i]
        head = QLabel('<span style="font-family:\'IBM Plex Mono\',monospace;font-size:10px;letter-spacing:3px;'
                      'color:#C9A24A;">THE NAVIGATOR’S TRIAL · %d OF %d</span><br>'
                      '<span style="font-family:Fraunces,Georgia,serif;font-size:20px;">%s</span>'
                      % (self.i+1, len(self.qs), q))
        head.setWordWrap(True); self.v.addWidget(head)
        for j, o in enumerate(opts):
            b = QPushButton(o); b.setStyleSheet('text-align:left;padding:11px 15px;')
            b.clicked.connect(lambda _, jj=j: self.answer(jj))
            self.v.addWidget(b)
        self.v.addStretch(1)
    def answer(self, j):
        q, opts, a = self.qs[self.i]
        ok = j == a
        if ok: self.score += 1
        self.main.snd.note(7) if ok else self.main.snd.thud()
        for k in range(self.v.count()):
            w = self.v.itemAt(k).widget()
            if isinstance(w, QPushButton):
                idx = self.v.indexOf(w)-1  # option index (after head label)
                w.setEnabled(False)
                if idx == a: w.setStyleSheet('text-align:left;padding:11px 15px;border-color:#E8C877;color:#E8C877;')
                elif idx == j: w.setStyleSheet('text-align:left;padding:11px 15px;border-color:#D95F4A;color:#D95F4A;')
                else: w.setStyleSheet('text-align:left;padding:11px 15px;opacity:.35;')
        QTimer.singleShot(850 if ok else 1400, self.next_q)
    def next_q(self):
        self.i += 1
        if self.i >= len(self.qs): self.done_(); return
        self.show_q()
    def done_(self):
        n = len(self.qs); s = self.score
        tier = 3 if s >= n-1 else 2 if s >= math.ceil(n*0.62) else 1 if s >= math.ceil(n*0.4) else 0
        names = ['Apprentice of the Night','Worthy Navigator','Skilled Navigator','Master Navigator']
        flavor = ['Every navigator began lost. The sky is patient.',
                  'The atlas has taught you well — and more remains.',
                  'A sure hand and a watchful eye.','The sky has few secrets left from you.']
        self.main.save['trial'] = max(self.main.save['trial'], tier); persist(self.main.save)
        if tier == 3: self.main.grant('master')
        while self.v.count():
            it = self.v.takeAt(0); w = it.widget()
            if w: w.deleteLater()
        head = QLabel('<span style="font-family:\'IBM Plex Mono\',monospace;font-size:10px;letter-spacing:3px;'
                      'color:#C9A24A;">THE TRIAL — COMPLETE</span><br><br>'
                      '<span style="font-family:Fraunces,Georgia,serif;font-size:26px;">%d of %d — %s</span><br><br>'
                      '<i style="color:rgba(231,221,196,.8);">%s</i><br><br>'
                      '<span style="font-family:\'IBM Plex Mono\',monospace;font-size:10px;color:rgba(231,221,196,.45);">'
                      'Best seal earned: %s</span>'
                      % (s, n, names[tier], flavor[tier],
                         names[self.main.save['trial']] if self.main.save['trial'] else '—'))
        head.setWordWrap(True); self.v.addWidget(head)
        row = QHBoxLayout(); row.addStretch(1)
        b1 = QPushButton('Sit the trial again'); b1.clicked.connect(self.again)
        b2 = QPushButton('Leave the hall'); b2.setObjectName('primary'); b2.clicked.connect(self.close)
        row.addWidget(b1); row.addWidget(b2); self.v.addLayout(row)
    def again(self):
        self.qs = self.make_pool()[:8]; random.shuffle(self.qs); self.qs = self.qs[:8]
        self.i = 0; self.score = 0; self.show_q()

class WheelDialog(QDialog):
    def __init__(self, main, lv):
        super().__init__(main)
        self.main = main; self.lv = lv
        self.north = lv['id'] != 'crux'
        self.lat = (main.save.get('geo') or {}).get('lat', 45 if self.north else -45)
        self.setWindowTitle('The wheel of the pole — %s' % lv['name'])
        self.setModal(True); self.resize(560, 680)
        v = QVBoxLayout(self); v.setContentsMargins(30, 24, 30, 20)
        head = QLabel('<span style="font-family:\'IBM Plex Mono\',monospace;font-size:10px;letter-spacing:3px;color:#C9A24A;">'
                      'THE WHEEL OF THE POLE</span><br><span style="font-family:Fraunces,Georgia,serif;font-size:24px;">'
                      'Why the %s never %s</span>' % (lv['name'], 'sets' if self.north else 'leaves'))
        head.setWordWrap(True); v.addWidget(head)
        self.cv = QLabel(); self.cv.setAlignment(Qt.AlignCenter); v.addWidget(self.cv, 1)
        row = QHBoxLayout(); row.addStretch(1)
        self.playing = True
        b = QPushButton('Pause'); b.setFixedWidth(100)
        b.clicked.connect(lambda: (setattr(self, 'playing', not self.playing),
                                   b.setText('Resume' if not self.playing else 'Pause')))
        row.addWidget(b); row.addStretch(1); v.addLayout(row)
        hor = 90-abs(self.lat)
        foot = ('Every star rides a circle around the pole. A circle entirely above your horizon never sets — that is '
                'what <i>circumpolar</i> means. From %.0f° N the horizon cuts the wheel %.0f° from the pole: everything '
                'inside the dashed ring is yours all night, every night.' % (abs(self.lat), hor)
                if self.north else
                'From %.0f° S the Cross wheels close around the southern sky and barely sets at all — which is why the '
                'anchor and the fish-hook hang steady for southern navigators.' % abs(self.lat))
        foot += (' One full turn of this model stands for the sidereal day: 23ʰ56ᵐ — the sky’s own clock.')
        ft = QLabel(foot); ft.setWordWrap(True)
        ft.setStyleSheet('font-size:12px;color:rgba(231,221,196,.6);font-style:italic;')
        v.addWidget(ft)
        self.rot = 0.0
        self.t = QTimer(self); self.t.timeout.connect(self.step); self.t.start(33)
        self._prev = time.perf_counter()
        self.step()
    def step(self):
        if not self.isVisible(): return
        tn = time.perf_counter(); dt = clamp(tn-self._prev, 0, 0.1); self._prev = tn
        if self.playing and not self.main.reduced: self.rot = (self.rot+dt*(360/16.0)) % 360
        S_ = 400
        pm = QPixmap(S_, S_); pm.fill(QColor('#04070f'))
        p = QPainter(pm); p.setRenderHint(QPainter.Antialiasing)
        cx = cy = S_/2; R = S_/2-16; SCOPE = 68.0
        lv = self.lv; mp = lv['map']; fig = [s for s in lv['stars'] if s['figure']]
        extras = POLE_N if self.north else POLE_S
        rings = [30, 45, 60, 75] if self.north else [-30, -45, -60, -75]
        f = QFont(); f.setFamilies(['IBM Plex Mono', 'Consolas', 'monospace']); f.setPixelSize(9)
        for d in rings:
            r = (90-abs(d))/SCOPE*R
            p.setPen(QPen(QColor(201, 162, 74, 26), 1)); p.setBrush(Qt.NoBrush)
            p.drawEllipse(QPointF(cx, cy), r, r)
            p.setPen(QColor(201, 162, 74, 90)); p.drawText(QPointF(cx+r+4, cy-4), 'δ %d°' % d)
        horR = (90-abs(self.lat))/SCOPE*R
        if horR < R+2 and abs(self.lat) > 4:
            pen = QPen(QColor(224, 122, 63, 115), 1, Qt.DashLine); p.setPen(pen)
            p.drawEllipse(QPointF(cx, cy), horR, horR)
            p.setPen(QColor(224, 122, 63, 153)); p.drawText(QPointF(cx-90, cy-horR-8),
                'your horizon · %.0f° %s' % (abs(self.lat), 'N' if self.lat >= 0 else 'S'))
        p.setPen(Qt.NoPen); p.setBrush(QColor(232, 200, 119, 230))
        p.drawEllipse(QPointF(cx, cy), 2.4, 2.4)
        p.setPen(QColor(201, 162, 74, 153))
        p.drawText(QPointF(cx-80, cy+16), 'NORTH CELESTIAL POLE' if self.north else 'SOUTH CELESTIAL POLE')
        def P(ra, dec):
            dp = clamp((90-dec) if self.north else (dec+90), 0, 89.5)/SCOPE*R
            a = (ra*15 + (-self.rot if self.north else self.rot))*DEG
            return QPointF(cx+math.sin(a)*dp, cy-math.cos(a)*dp)
        for s in fig:
            pt = P(s['ra'], s['dec'])
            r = math.hypot(pt.x()-cx, pt.y()-cy)
            p.setPen(QPen(QColor(232, 200, 119, 36), 1)); p.setBrush(Qt.NoBrush)
            ang = math.degrees(math.atan2(pt.y()-cy, pt.x()-cx))
            p.drawArc(QRectF(cx-r, cy-r, r*2, r*2), int((ang-0.9)*16), int(0.9*16))
        p.setPen(QPen(QColor(236, 208, 140, 204), 1.1))
        for a, b in lv['edges']:
            A = mp.get(a); B = mp.get(b)
            if not A or not B: continue
            p.drawLine(P(A['ra'], A['dec']), P(B['ra'], B['dec']))
        for s in extras:
            pt = P(s['ra'], s['dec']); r = clamp(2.6-(s['mag']-1)*0.3, 1.2, 3.4)
            p.setOpacity(.9)
            p.drawPixmap(QRectF(pt.x()-r*4, pt.y()-r*4, r*8, r*8), SPR.star_pix(SPEC[s['cls']]), QRectF(0, 0, 96, 96))
            p.setOpacity(1)
            if s['id'] in ('polaris', 'sigmaoct'):
                p.setPen(QColor(233, 224, 199, 217))
                fo = QFont(); fo.setFamilies(['Fraunces', 'Georgia', 'serif']); fo.setItalic(True); fo.setPixelSize(11)
                p.setFont(fo)
                p.drawText(pt+QPointF(7, -6), s['name']+' · %s' % ('0.7° from the pole' if self.north else '5° from the pole'))
        for s in fig:
            pt = P(s['ra'], s['dec']); r = clamp(2.8-(s['mag']-1)*0.28, 1.4, 3.6)
            p.setOpacity(.5)
            p.drawPixmap(QRectF(pt.x()-r*6, pt.y()-r*6, r*12, r*12), SPR.ember_pix(), QRectF(0, 0, 96, 96))
            p.setOpacity(1)
            p.drawPixmap(QRectF(pt.x()-r*4, pt.y()-r*4, r*8, r*8), SPR.star_pix(SPEC[s['cls']]), QRectF(0, 0, 96, 96))
            p.setPen(QColor(233, 224, 199, 204))
            fo = QFont(); fo.setFamilies(['Fraunces', 'Georgia', 'serif']); fo.setItalic(True); fo.setPixelSize(10)
            p.setFont(fo); p.drawText(pt+QPointF(6, 4), s['name'])
        p.end()
        self.cv.setPixmap(pm)

# ============================== plate rendering (cards & poster) ==============================
def draw_plate_into(p, lv, idx, x, y, w, h, bg=True):
    if bg: p.fillRect(QRectF(x, y, w, h), QColor('#04070f'))
    rng = mulberry32(lv['seed']+7)
    p.setOpacity(1)
    for _ in range(70):
        px, py = x+rng()*w, y+rng()*h
        r = 0.3+rng()*0.8; a = 0.08+rng()*0.3
        p.setOpacity(a)
        p.drawPixmap(QRectF(px-r*6, py-r*6, r*12, r*12), SPR.star_pix('#dfe6f5'), QRectF(0, 0, 96, 96))
    p.setOpacity(1)
    fig = [s for s in lv['stars'] if s['figure']]
    cos = math.cos(lv['center'][1]*DEG)
    pts = [((s['ra']-lv['center'][0] - round((s['ra']-lv['center'][0])/24)*24)*15*cos, s['dec']-lv['center'][1])
           for s in fig]
    x0 = min(q[0] for q in pts); x1 = max(q[0] for q in pts)
    y0 = min(q[1] for q in pts); y1 = max(q[1] for q in pts)
    sc = min((w-56)/max(0.001, x1-x0), (h-52)/max(0.001, y1-y0))
    def X(q): return x+w/2+(q[0]-(x0+x1)/2)*sc
    def Y(q): return y+h/2-(q[1]-(y0+y1)/2)*sc
    pos = {s['id']: QPointF(X(pts[i]), Y(pts[i])) for i, s in enumerate(fig)}
    p.setPen(QPen(QColor(232, 200, 119, 191), 0.9))
    for a, b in lv['edges']:
        A = pos.get(a); B = pos.get(b)
        if A and B: p.drawLine(A, B)
    best = min(fig, key=lambda s: s['mag'])
    fo = QFont(); fo.setFamilies(['Fraunces', 'Georgia', 'serif']); fo.setItalic(True); fo.setPixelSize(10)
    for s in fig:
        pt = pos[s['id']]; r = clamp(2.6-(s['mag']-1)*0.3, 1.1, 3.4)
        p.setPen(Qt.NoPen)
        p.drawPixmap(QRectF(pt.x()-r*4, pt.y()-r*4, r*8, r*8), SPR.star_pix(SPEC[s['cls']]), QRectF(0, 0, 96, 96))
        if s is best:
            p.setPen(QColor(232, 200, 119, 217)); p.setFont(fo)
            p.drawText(pt+QPointF(8, -4), s['name'])
    f2 = QFont(); f2.setFamilies(['IBM Plex Mono', 'Consolas', 'monospace']); f2.setPixelSize(9)
    p.setFont(f2); p.setPen(QColor(201, 162, 74, 102))
    p.drawText(QPointF(x+w-34, y+14), 'PL. '+rom(idx))

# ============================== title & finale dialogs ==============================
class TitleDialog(QDialog):
    def __init__(self, main):
        super().__init__(main)
        self.main = main
        self.setWindowTitle('Asterisma')
        self.setModal(True); self.resize(680, 660)
        v = QVBoxLayout(self); v.setContentsMargins(40, 34, 40, 26); v.setSpacing(8)
        t1 = QLabel('A FIELD ATLAS OF THE NIGHT')
        t1.setStyleSheet("font-family:'IBM Plex Mono',monospace;font-size:10px;letter-spacing:6px;color:#C9A24A;")
        t1.setAlignment(Qt.AlignCenter); v.addWidget(t1)
        big = QLabel('Asterisma')
        big.setStyleSheet("font-family:Fraunces,Georgia,serif;font-weight:300;font-size:72px;"
                          "color:#F2E6C8;background:transparent;")
        big.setAlignment(Qt.AlignCenter); v.addWidget(big)
        lede = QLabel('Every pattern below was first traced by someone looking up — to sow, to sail, to grieve, '
                      'to steer. %s skies. Many cultures. One atlas, to be finished by your hand.'
                      % (NUMWORD[len(LEVELS)] if len(LEVELS) < len(NUMWORD) else str(len(LEVELS))))
        lede.setWordWrap(True); lede.setAlignment(Qt.AlignCenter)
        lede.setStyleSheet('font-style:italic;font-weight:300;font-size:16px;color:rgba(231,221,196,.65);')
        v.addWidget(lede); v.addSpacing(8)
        row = QHBoxLayout(); row.addStretch(1)
        self.primary = QPushButton('Begin the atlas'); self.primary.setObjectName('primary')
        self.primary.clicked.connect(self._primary); row.addWidget(self.primary)
        b2 = QPushButton('What’s up tonight?'); b2.clicked.connect(lambda: (self.close(), main.open_tonight()))
        row.addWidget(b2)
        b3 = QPushButton('How to chart'); b3.clicked.connect(lambda: (self.close(), main.open_help()))
        row.addWidget(b3)
        b4 = QPushButton('The Navigator’s Trial'); b4.clicked.connect(lambda: main.open_trial())
        row.addWidget(b4); row.addStretch(1)
        v.addLayout(row)
        row2 = QHBoxLayout(); row2.addStretch(1)
        self.bIndex = QPushButton('Plate index'); self.bIndex.clicked.connect(lambda: main.open_atlas())
        self.bVault = QPushButton('Walk the whole vault'); self.bVault.clicked.connect(lambda: (self.close(), main.load_tour()))
        self.bAnew = QPushButton('Begin anew'); self.bAnew.clicked.connect(main.begin_anew)
        bExp = QPushButton('copy atlas code'); bExp.clicked.connect(main.export_code)
        bImp = QPushButton('restore a code'); bImp.clicked.connect(main.import_code)
        for b in (self.bIndex, self.bVault, self.bAnew, bExp, bImp):
            b.setStyleSheet('font-size:10px;padding:6px 12px;'); row2.addWidget(b)
        row2.addStretch(1); v.addLayout(row2)
        v.addSpacing(6)
        self.strip = QHBoxLayout(); self.strip.setSpacing(6); v.addLayout(self.strip)
        self.prog = QLabel(); self.prog.setAlignment(Qt.AlignCenter)
        self.prog.setStyleSheet("font-family:'IBM Plex Mono',monospace;font-size:10px;letter-spacing:3px;"
                                "color:rgba(231,221,196,.4);text-transform:uppercase;")
        v.addWidget(self.prog)
        v.addStretch(1)
        ft = QLabel('The stars are plotted at their true places (J2000) · the Moon and planets are drawn where they are tonight.<br>'
                    'The stories belong to everyone who ever needed the dark · sound on is worth it')
        ft.setAlignment(Qt.AlignCenter)
        ft.setStyleSheet("font-family:'IBM Plex Mono',monospace;font-size:9.5px;color:rgba(231,221,196,.4);")
        v.addWidget(ft)
        self.refresh()
    def refresh(self):
        main = self.main
        n = next((i for i, lv in enumerate(LEVELS) if lv['id'] not in main.save['done']), None)
        if n is None:
            self.primary.setText('The finished atlas')
        else:
            self.primary.setText('Begin the atlas' if n == 0 else 'Continue — Plate %s' % rom(n+1))
        self._next = n
        any_done = bool(main.save['done'])
        self.bIndex.setVisible(any_done); self.bAnew.setVisible(any_done)
        self.bVault.setVisible(n is None)
        dn = sum(1 for lv in LEVELS if lv['id'] in main.save['done'])
        fl = sum(1 for lv in LEVELS if main.save['done'].get(lv['id'], {}).get('stars') == 3)
        an = sum(1 for a in ACHS if main.save['ach'].get(a[0]))
        self.prog.setText('%d of %d plates charted · %d flawless · %d of %d honours'
                          % (dn, len(LEVELS), fl, an, len(ACHS)))
        while self.strip.count():
            it = self.strip.takeAt(0); w = it.widget()
            if w: w.deleteLater()
        for i, lv in enumerate(LEVELS):
            d = main.save['done'].get(lv['id'])
            b = QPushButton('%s\n%s' % (lv['numeral'], ('★'*d['stars']+'·'*(3-d['stars'])) if d else '· · ·'))
            b.setFixedWidth(52)
            b.setStyleSheet('font-family:Fraunces,Georgia,serif;font-style:italic;font-size:14px;padding:6px 4px;'
                            + ('color:#E8C877;border-color:rgba(201,162,74,50%);' if d else ''))
            if main.unlocked(i):
                b.clicked.connect(lambda _, ii=i: (self.close(), main.load_level(ii)))
            else:
                b.setEnabled(False)
            self.strip.addWidget(b)
    def _primary(self):
        self.close()
        if self._next is None: self.main.show_finale()
        else: self.main.load_level(self._next)

class FinaleDialog(QDialog):
    def __init__(self, main):
        super().__init__(main)
        self.main = main
        self.setWindowTitle('The atlas is complete')
        self.setModal(True); self.resize(880, 760)
        v = QVBoxLayout(self); v.setContentsMargins(34, 28, 34, 22)
        head = QLabel('<div style="text-align:center;">'
                      '<span style="font-family:\'IBM Plex Mono\',monospace;font-size:10px;letter-spacing:4px;color:#C9A24A;">'
                      'THE ATLAS IS COMPLETE</span><br>'
                      '<span style="font-family:Fraunces,Georgia,serif;font-size:38px;">%s skies, charted by hand</span><br>'
                      '<span style="font-family:\'IBM Plex Mono\',monospace;font-size:11px;color:rgba(231,221,196,.62);">%s</span></div>'
                      % (NUMWORD[len(LEVELS)],
                         self._stats()))
        head.setWordWrap(True); v.addWidget(head)
        sc = QScrollArea(); sc.setWidgetResizable(True); sc.setFrameShape(QFrame.NoFrame)
        inner = QWidget(); g = QGridLayout(inner); g.setSpacing(14)
        totS = sum(len([s for s in lv['stars'] if s['figure']]) for lv in LEVELS)
        for i, lv in enumerate(LEVELS):
            d = main.save['done'].get(lv['id'], {})
            stars = d.get('stars', 0)
            pm = QPixmap(int(300*self.devicePixelRatioF()), int(172*self.devicePixelRatioF()))
            pm.setDevicePixelRatio(self.devicePixelRatioF())
            pm.fill(Qt.transparent)
            p = QPainter(pm); p.setRenderHint(QPainter.Antialiasing)
            p.setRenderHint(QPainter.SmoothPixmapTransform)
            draw_plate_into(p, lv, i+1, 0, 0, 300, 172); p.end()
            img = QLabel(); img.setPixmap(pm); img.setFixedSize(300, 172)
            img.setStyleSheet('border:1px solid rgba(201,162,74,26%);background:rgba(8,13,26,.7);')
            cap = QLabel('<b style="font-family:Fraunces,Georgia,serif;font-weight:400;">%s</b> '
                         '<i style="color:rgba(231,221,196,.6);">· %s</i> &nbsp;'
                         '<span style="color:#E8C877;">%s</span>'
                         % (lv['name'], lv['common'], '★'*stars+'·'*(3-stars)))
            vb = QVBoxLayout(); vb.addWidget(img); vb.addWidget(cap)
            w = QWidget(); w.setLayout(vb)
            g.addWidget(w, i//3, i % 3)
        sc.setWidget(inner); v.addWidget(sc, 1)
        ach = QLabel(' '.join(
            '<span style="%s"><b>%s %s</b> <span style="color:rgba(231,221,196,.55);font-size:11.5px;">%s</span></span>'
            % ('' if main.save['ach'].get(a[0]) else 'opacity:.3;',
               a[3], a[1], a[2]) for a in ACHS))
        ach.setWordWrap(True); ach.setStyleSheet('font-size:12.5px;')
        v.addWidget(ach)
        tail = QLabel('<i style="color:rgba(231,221,196,.65);">Every figure here was first named by someone who needed '
                      'the dark. The sky keeps them all — and now, partly, so do you.</i>')
        tail.setWordWrap(True); v.addWidget(tail)
        row = QHBoxLayout(); row.addStretch(1)
        b1 = QPushButton('Take the atlas as a keepsake'); b1.clicked.connect(main.take_poster)
        b2 = QPushButton('Walk the whole vault'); b2.clicked.connect(lambda: (self.close(), main.load_tour()))
        b3 = QPushButton('Return to the beginning'); b3.setObjectName('primary')
        b3.clicked.connect(lambda: (self.close(), main.show_title()))
        for b in (b1, b2, b3): row.addWidget(b)
        row.addStretch(1); v.addLayout(row)
    def _stats(self):
        main = self.main
        totS = sum(len([s for s in lv['stars'] if s['figure']]) for lv in LEVELS)
        totL = sum(len(lv['edges']) for lv in LEVELS)
        hon = sum(d.get('stars', 0) for d in main.save['done'].values())
        trial = ['—','Apprentice of the Night','Worthy Navigator','Skilled Navigator','Master Navigator']
        s = '%d stars · %d lines · %d of %d honours' % (totS, totL, hon, len(LEVELS)*3)
        if main.save['trial'] > 0: s += ' · trial: '+trial[main.save['trial']]
        return s

class AchievementsDialog(PanelDialog):
    def __init__(self, main):
        super().__init__(main, 'Asterisma — honours')
        rows = ''
        for a in ACHS:
            got = main.save['ach'].get(a[0])
            rows += ('<div style="display:flex;gap:12px;padding:9px 2px;border-bottom:1px solid rgba(201,162,74,12%);%s">'
                     '<span style="color:#E8C877;">%s</span><div><b>%s</b><br>'
                     '<span style="font-size:12px;color:rgba(231,221,196,.6);">%s</span></div></div>'
                     % ('' if got else 'opacity:.3;', a[3], a[1], a[2]))
        self.body.setHtml(page(over('honours') + h1('What the atlas remembers', sm=True) +
                               '<hr style="border:none;border-top:1px solid rgba(201,162,74,26%);">' + rows))
        self.add_btn('Close', self.close)

# ============================== main window ==============================
APP_CSS = """
* { font-family: 'Spectral','Georgia',serif; color:#e7ddc4; font-size:14px; }
QMainWindow, QDialog { background-color:#050a14; }
QDialog { border:1px solid rgba(201,162,74,60); }
QLabel { background:transparent; }
QPushButton { background:transparent; border:1px solid rgba(201,162,74,66); padding:10px 22px;
  font-family:'Fraunces','Georgia',serif; font-size:12px; color:#e7ddc4; }
QPushButton:hover { border-color:#E8C877; background:rgba(201,162,74,24); }
QPushButton#primary { color:#E8C877; border-color:rgba(201,162,74,128); }
QPushButton:disabled { opacity:.4; }
QToolBar { background:#050a14; border:none; border-bottom:1px solid rgba(201,162,74,26%); spacing:8px; padding:8px 14px; }
QToolButton { background:transparent; border:1px solid rgba(201,162,74,66); padding:5px 9px;
  font-family:'IBM Plex Mono',monospace; font-size:10px; color:rgba(231,221,196,.72); }
QToolButton:hover { color:#e7ddc4; border-color:#E8C877; }
QToolButton:checked { color:#E8C877; border-color:rgba(201,162,74,128); background:rgba(201,162,74,20); }
QDockWidget { color:#C9A24A; font-family:'IBM Plex Mono',monospace; font-size:9px;
  titlebar-close-icon: none; }
QDockWidget::title { background:rgba(9,14,27,225); border:1px solid rgba(201,162,74,26%); padding:7px 12px; text-align:left; }
QTextEdit, QTextBrowser, QListWidget, QLineEdit { background:rgba(8,13,26,180); border:1px solid rgba(201,162,74,26%);
  selection-background-color:rgba(201,162,74,60); }
QTextEdit, QTextBrowser { border:none; }
QLineEdit { padding:8px 10px; font-family:'IBM Plex Mono',monospace; font-size:12px; }
QStatusBar { background:#050a14; border-top:1px solid rgba(201,162,74,20%); }
QStatusBar QLabel { font-family:'IBM Plex Mono',monospace; font-size:10.5px; color:rgba(231,221,196,.62); padding:0 8px; }
#tipBox { background:rgba(9,14,27,232); border:1px solid rgba(201,162,74,26%); padding:10px 13px;
  font-size:12.5px; max-width:270px; }
#tipBox .m { font-family:'IBM Plex Mono',monospace; font-size:11px; color:rgba(231,221,196,.62); }
#toastBox { background:rgba(9,14,27,235); border:1px solid rgba(201,162,74,26%); padding:9px 18px;
  font-family:'IBM Plex Mono',monospace; font-size:11px; color:#e7ddc4; }
#taleBox { background:rgba(9,14,27,225); }
a { color:#E8C877; text-decoration:none; }
a.btnlink { display:inline-block; border:1px solid rgba(201,162,74,66); padding:8px 16px;
  font-family:'Fraunces',Georgia,serif; font-size:12px; margin:2px 0; }
a.btnlink:hover { border-color:#E8C877; background:rgba(201,162,74,24); }
a.btnlink.primary { color:#E8C877; }
a.rowlink { display:block; padding:9px 4px; font-family:Fraunces,Georgia,serif; font-size:17px; color:#e7ddc4; }
a.rowlink:hover { background:rgba(201,162,74,15); }
kbd { border:1px solid rgba(201,162,74,66); padding:1px 5px; font-family:'IBM Plex Mono',monospace;
  font-size:10px; color:#E8C877; }
table th { color:rgba(231,221,196,.4); font-weight:400; }
td { padding:4px 8px 4px 0; border-top:1px solid rgba(201,162,74,12%); color:rgba(231,221,196,.75); }
td:first-child { color:#e7ddc4; font-family:Fraunces,Georgia,serif; font-size:13px; }
QScrollBar:vertical { background:transparent; width:6px; }
QScrollBar::handle:vertical { background:rgba(201,162,74,40%); min-height:24px; }
QScrollBar::add-line, QScrollBar::sub-line { height:0; }
"""

class Main(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle('Asterisma — a field atlas of the night')
        self.resize(1280, 800)
        self.save = load_save()
        self.scene = 'title'
        self.modal_ref = None
        self.reduced = False
        self.snd = Snd(); self.snd.set_muted(self.save['muted'])
        self.tts = Tts()
        build_wanderers()
        # central sky
        self.sky = SkyView(self)
        self.setCentralWidget(self.sky)
        self.sky.set_cam(OVERTURE['center'][0], OVERTURE['center'][1], OVERTURE['view'])
        # toolbar
        tb = QToolBar(); tb.setMovable(False); tb.setFloatable(False)
        self.addToolBar(Qt.TopToolBarArea, tb)
        self.brand = QLabel('  A S T E R I S M A')
        self.brand.setStyleSheet("font-family:Fraunces,Georgia,serif;font-weight:600;font-size:12px;"
                                 "letter-spacing:2px;color:#e7ddc4;")
        tb.addWidget(self.brand)
        self.plate_tag = QLabel('')
        self.plate_tag.setStyleSheet("font-family:'IBM Plex Mono',monospace;font-size:10px;"
                                     "color:rgba(231,221,196,.38);")
        tb.addWidget(self.plate_tag)
        spacer = QWidget(); spacer.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Preferred)
        tb.addWidget(spacer)
        self.act_hint = QAction('reveal a line · −1 ✦', self)
        self.act_hint.triggered.connect(self.reveal_hint)
        tb.addAction(self.act_hint)
        self.moon_btn = QToolButton(); self.moon_btn.setCheckable(False)
        self.moon_btn.clicked.connect(self.open_tonight)
        self.moon_btn.setToolTip('Tonight’s sky (T)')
        tb.addWidget(self.moon_btn)
        self.act_grid = QAction('grid', self); self.act_grid.setCheckable(True)
        self.act_grid.triggered.connect(self.toggle_grid); tb.addAction(self.act_grid)
        self.act_dark = QAction('dark sky', self); self.act_dark.setCheckable(True)
        self.act_dark.triggered.connect(self.toggle_dark); tb.addAction(self.act_dark)
        self.act_sq = QAction('sky ✦', self); self.act_sq.triggered.connect(self.cycle_sq); tb.addAction(self.act_sq)
        a_ch = QAction('chronicle', self); a_ch.triggered.connect(self.open_chronicle); tb.addAction(a_ch)
        a_h = QAction('help', self); a_h.triggered.connect(self.open_help); tb.addAction(a_h)
        a_a = QAction('atlas', self); a_a.triggered.connect(self.open_atlas); tb.addAction(a_a)
        self.act_snd = QAction('sound', self); self.act_snd.triggered.connect(self.toggle_sound); tb.addAction(self.act_snd)
        # dock: tale
        self.dock = QDockWidget('Tale & charting notes', self)
        self.dock.setFeatures(QDockWidget.DockWidgetMovable | QDockWidget.DockWidgetFloatable |
                              QDockWidget.DockWidgetClosable)
        tw = QWidget(); tw.setObjectName('taleBox')
        tv = QVBoxLayout(tw); tv.setContentsMargins(12, 4, 12, 10)
        self.tale_browser = QTextBrowser(); self.tale_browser.setOpenExternalLinks(False)
        self.tale_browser.anchorClicked.connect(self.handle_link)
        self.tale_browser.setMaximumHeight(220)
        tv.addWidget(self.tale_browser)
        trow = QHBoxLayout()
        self.tale_tab = QPushButton('read the tale')
        self.tale_tab.setStyleSheet('font-family:\'IBM Plex Mono\',monospace;font-size:9px;padding:3px 8px;')
        self.tale_tab.clicked.connect(self.toggle_tale)
        trow.addWidget(self.tale_tab)
        if self.tts.available():
            self.speak_btn = QPushButton('listen to the tale')
            self.speak_btn.setStyleSheet('font-family:\'IBM Plex Mono\',monospace;font-size:9px;padding:3px 8px;')
            self.speak_btn.clicked.connect(self.speak_tale)
            trow.addWidget(self.speak_btn)
        trow.addStretch(1); tv.addLayout(trow)
        self.dock.setWidget(tw)
        self.addDockWidget(Qt.BottomDockWidgetArea, self.dock)
        self.dock.hide()
        self.tale_mode = 'notes'
        # status bar
        sb = self.statusBar()
        self.lb_coords = QLabel('—'); self.lb_field = QLabel(''); self.lb_sky = QLabel('')
        self.lb_sep = QLabel(''); self.lb_sel = QLabel('no star chosen'); self.lb_lines = QLabel('')
        for w in (self.lb_coords, self.lb_field, self.lb_sky, self.lb_sep, self.lb_sel, self.lb_lines):
            sb.addPermanentWidget(w)
        self.toast_lbl = QLabel(self.sky); self.toast_lbl.setObjectName('toastBox')
        self.toast_lbl.setWordWrap(True); self.toast_lbl.hide()
        self.toast_timer = QTimer(self); self.toast_timer.setSingleShot(True)
        self.toast_timer.timeout.connect(self.toast_lbl.hide)
        # shortcuts
        for seq, fn in [('/', self.open_finder), ('?', self.open_help), ('T', self.open_tonight),
                        ('Q', self.cycle_sq), ('G', self.toggle_grid), ('D', self.toggle_dark),
                        ('0', lambda: self.sky.reset_view()), ('+', lambda: self.sky.zoom_at(self.sky.W/2, self.sky.H/2, 1.25)),
                        ('-', lambda: self.sky.zoom_at(self.sky.W/2, self.sky.H/2, 0.8)),
                        ('N', self.cycle_focus), ('Enter', self.enter_pick),
                        ('Return', self.enter_pick)]:
            sc = QShortcut(QKeySequence(seq), self); sc.activated.connect(fn)
        for key, dx, dy in [(Qt.Key_Left, 1, 0), (Qt.Key_Right, -1, 0), (Qt.Key_Up, 0, 1), (Qt.Key_Down, 0, -1)]:
            sc = QShortcut(QKeySequence(key), self)
            sc.activated.connect(lambda ddx=dx, ddy=dy: self.sky.pan_by(ddx*self.sky.cam['view']*0.12,
                                                                       ddy*self.sky.cam['view']*0.12))
        esc = QShortcut(QKeySequence(Qt.Key_Escape), self)
        esc.activated.connect(self.escape)
        self.apply_toggles()
        self.upd_sky_label()
        self.paint_moon_btn()
        self.show_title()
        self.title_dlg = TitleDialog(self)
        self.title_dlg.exec()

    # ---------- helpers for labels ----------
    def upd_field_label(self):
        v = self.sky.cam['view']
        self.lb_field.setText('field %s°' % ('%.1f' % v if v < 10 else '%d' % round(v)))
    def upd_sky_label(self):
        B = BORTLE[self.save.get('sq', 0)]
        self.lb_sky.setText('sky: '+B['n'])
    def set_coords(self, ra, dec):
        self.lb_coords.setText('α %s · δ %s' % (fmtRA(ra), fmtDec(dec)))
    def set_sel_label(self, s):
        if s is None:
            self.lb_sel.setText('no star chosen'); self.lb_sep.setText(''); return
        extra = ''
        if self.save.get('geo'):
            try:
                a = alt_of(self.save['geo']['lat'], self.save['geo']['lon'], s['ra']*15, s['dec'], astro())
                extra = (' · alt %d° %s' % (round(a['alt']), cardinal(a['az']))) if a['alt'] > 0 \
                        else ' · below your horizon'
            except Exception:
                pass
        self.lb_sel.setText('◉ %s — %s%s' % (s['name'], s['bayer'], extra))
    def update_sep(self):
        sel, hov = self.sky.sel, self.sky.hover
        if sel is None or hov is None or 'id' not in hov or hov is sel:
            self.lb_sep.setText(''); return
        d = angSep(sel, hov)
        self.lb_sep.setText('sep %s' % ('%d′' % round(d*60) if d < 1 else '%.1f°' % d))
    def update_hud(self):
        self.act_hint.setEnabled(self.sky.embers > 0 and self.sky.phase == 'playing'
                                 and not self.sky.cfg.get('explore') and not self.sky.cfg.get('tour'))
        self.lb_lines.setText('lines %d / %d' % (len(self.sky.drawn), len(self.sky.cfg['edges'])))
    def toast(self, msg):
        self.toast_lbl.setText(msg)
        self.toast_lbl.adjustSize()
        self.toast_lbl.move((self.sky.W-self.toast_lbl.width())//2,
                            self.sky.H-self.toast_lbl.height()-70)
        self.toast_lbl.show(); self.toast_lbl.raise_()
        self.toast_timer.start(3000)
    def modal_open(self):
        return QApplication.activeModalWidget() is not None

    # ---------- achievements ----------
    def grant(self, id_):
        if self.save['ach'].get(id_): return
        self.save['ach'][id_] = True; persist(self.save)
        a = next((x for x in ACHS if x[0] == id_), None)
        if a: self.toast('Achievement — %s' % a[1])
    def ach_checks(self):
        self.grant('firstlight')
        if self.sky.lapses == 0: self.grant('steadyhand')
        if all(self.save['done'].get(lv['id'], {}).get('stars') == 3 for lv in LEVELS): self.grant('untarnished')
        if self.save.get('dark'): self.grant('darklight')
        if self.save.get('sq', 0) >= len(BORTLE)-1: self.grant('citylight')

    # ---------- flow ----------
    def show_title(self):
        self.scene = 'title'
        self.sky.phase = 'title'
        self.sky.cfg = OVERTURE
        self.sky.load_config(OVERTURE)
        self.plate_tag.setText('')
        self.dock.hide()
    def load_level(self, i, explore=False, skip_intro=False):
        self.close_modals()
        self.scene = 'game'
        lv = LEVELS[i]
        self.sky.load_config(lv, explore)
        self.plate_tag.setText(' · Plate %s of %s%s' % (lv['numeral'], rom(len(LEVELS)),
                                                        ' · study' if explore else ''))
        self.dock.show()
        self.fill_tale(lv)
        self.update_hud()
        self.lb_lines.setText('lines %d / %d' % (len(self.sky.drawn), len(lv['edges'])))
        if explore:
            self.toast('A study chart — pan and zoom freely; hover anything.')
            QTimer.singleShot(650, lambda: StudyDialog(self, lv, True).exec())
        elif not skip_intro:
            PlateDialog(self, lv).exec()
    def begin_charting(self):
        self.close_modals()
        self.sky.phase = 'playing'
        self.sky.breath_at = time.perf_counter()
        self.sky.chart_start = time.perf_counter()
        if self.width() < 800: self.dock.hide()
        if not self.save['seen']:
            self.save['seen'] = True; persist(self.save)
            QTimer.singleShot(700, lambda: self.toast(
                'Hover any star to learn it — the ember-lit ones belong to the figure.'))
    def on_plate_complete(self):
        secs = time.perf_counter()-self.sky.chart_start
        starsN = 3 if self.sky.lapses == 0 else 2 if self.sky.lapses <= 2 else 1
        lv = self.sky.cfg
        prev = self.save['done'].get(lv['id'], {}).get('stars', 0)
        self.save['done'][lv['id']] = {'stars': max(starsN, prev), 'lapses': self.sky.lapses,
                                       'dark': bool(self.save.get('dark'))}
        b = self.save['best'].get(lv['id'])
        self.save['best'][lv['id']] = min(b, secs) if b else secs
        persist(self.save); self.ach_checks(); self.update_hud()
        self.sky.shower_until = time.perf_counter()+2.6
        QTimer.singleShot(int(300+len(lv['edges'])*140+300), self.snd.chord)
        idx = next(i for i, x in enumerate(LEVELS) if x['id'] == lv['id'])
        QTimer.singleShot(int(300+len(lv['edges'])*140+1500),
                          lambda: StudyDialog(self, LEVELS[idx], False, starsN).exec())
    def night_dims(self):
        if self.sky.phase != 'fading': return
        self.sky.phase = 'dims'; self.snd.dark()
        d = PanelDialog(self, 'the night dims')
        d.body.setHtml(page(over('the night dims') + h1('The last ember has gone out', sm=True) +
                            '<hr style="border:none;border-top:1px solid rgba(201,162,74,26%);">' +
                            tale_p('The figure fades back into the field of stars. The stars are patient — '
                                   'reread the tale, mind the ember-light, and begin again.')))
        d.add_btn('Plate index', lambda: (d.close(), self.open_atlas()))
        def relight():
            d.close()
            self.load_level(next(i for i, x in enumerate(LEVELS) if x['id'] == self.sky.cfg['id']),
                            skip_intro=True)
            self.toast('The embers are relit.')
        d.add_btn('Relight the embers', relight, primary=True)
        d.exec()
    def reveal_hint(self):
        sv = self.sky
        if sv.phase != 'playing' or sv.embers < 1 or sv.cfg.get('explore') or sv.cfg.get('tour'): return
        for a, b in sv.cfg['edges']:
            if ekey(a, b) not in sv.drawn_set:
                A, B = sv.cfg['map'][a], sv.cfg['map'][b]
                sv.hint = {'a': A, 'b': B, 'until': time.perf_counter()+3.4}
                sv.embers -= 1; sv.lapses += 1
                self.snd.tick(); self.update_hud()
                sep = angSep(A, B)
                mid_ra = mod24(A['ra']+deltaH(B['ra'], A['ra'])/2)
                v = clamp(max(sep*3, sv.cam['view']*0.5), sv.cfg['viewMin']*sv.cfg['view'], sv.cfg['view'])
                sv.fly_to(mid_ra, (A['dec']+B['dec'])/2, v)
                return
    def cycle_focus(self):
        fig = [s for s in self.sky.named if s.get('figure')]
        if not fig: return
        i = fig.index(self.sky.focus_star) if self.sky.focus_star in fig else -1
        self.sky.focus_star = fig[(i+1) % len(fig)]
        self.snd.tick()
        fs = self.sky.focus_star
        if fs['_x'] < -20 or fs['_x'] > self.sky.W+20 or fs['_y'] < -20 or fs['_y'] > self.sky.H+20:
            self.sky.fly_to(fs['ra'], fs['dec'], self.sky.cam['view'])
    def enter_pick(self):
        fs = self.sky.focus_star
        if fs is None: return
        if self.sky.sel is None: self.sky.select_star(fs)
        elif self.sky.sel is not fs:
            a, b = self.sky.sel, fs
            self.sky.clear_sel(); self.sky.attempt(a, b); self.sky.focus_star = None
    def load_tour(self):
        self.close_modals()
        self.scene = 'game'
        self.sky.load_config(TOUR)
        self.sky.drawn = [{'a': a, 'b': b, 't0': 0.0} for a, b in TOUR['edges']]
        self.sky.drawn_set = set(self.sky.edge_set)
        self.plate_tag.setText(' · the whole vault')
        self.dock.hide()
        self.update_hud()
        self.snd.chord(); self.grant('vault')
        self.toast('%d figures, one sky — the plates were always pieces of this.' % len(LEVELS))
        self.lb_lines.setText('lines %d / %d' % (len(TOUR['edges']), len(TOUR['edges'])))

    # ---------- toggles ----------
    def apply_toggles(self):
        self.act_grid.setChecked(bool(self.save.get('grid')))
        self.act_dark.setChecked(bool(self.save.get('dark')))
        self.act_snd.setText('muted' if self.save['muted'] else 'sound')
        self.sky.dirty = True
    def toggle_grid(self):
        self.save['grid'] = not self.save.get('grid'); persist(self.save); self.apply_toggles()
        self.toast('The grid of the sphere — right ascension and declination.' if self.save['grid']
                   else 'The grid is stowed.')
    def toggle_dark(self):
        self.save['dark'] = not self.save.get('dark'); persist(self.save); self.apply_toggles()
        self.toast('Dark-sky mode — the ember-light dims, and so does the chrome. Chart by wit.'
                   if self.save['dark'] else 'The sky returns to its ordinary dark.')
    def toggle_sound(self):
        self.save['muted'] = not self.save['muted']; persist(self.save)
        self.snd.set_muted(self.save['muted']); self.apply_toggles()
    def cycle_sq(self):
        self.save['sq'] = (self.save.get('sq', 0)+1) % len(BORTLE)
        persist(self.save); self.upd_sky_label(); self.apply_toggles()
        self.snd.tick(); self.toast(BORTLE[self.save['sq']]['msg'])

    # ---------- tale ----------
    def fill_tale(self, lv):
        self.tale_mode = 'notes'
        self.render_tale(lv)
    def render_tale(self, lv=None):
        lv = lv or self.sky.cfg
        if self.tale_mode == 'story':
            self.tale_browser.setHtml(page(tale_p(lv['tale'])))
            self.tale_tab.setText('back to the notes')
            self.save.setdefault('read', {})[lv['id']] = 1; persist(self.save)
            if all(self.save['read'].get(x['id']) for x in LEVELS): self.grant('storykeeper')
        else:
            self.tale_browser.setHtml(page(''.join(
                '<div style="display:flex;gap:9px;margin:8px 0;color:rgba(231,221,196,.75);">'
                '<span style="color:#C9A24A;">✦</span><span>%s</span></div>' % n for n in lv['notes'])))
            self.tale_tab.setText('read the tale')
    def toggle_tale(self):
        self.tale_mode = 'story' if self.tale_mode == 'notes' else 'notes'
        self.render_tale()
    def speak_tale(self):
        if not self.tts.available():
            self.toast('This build has no speech engine — QtTextToSpeech is needed.'); return
        if self.tts.speaking:
            self.tts.stop(); return
        if self.tts.speak(self.sky.cfg['tale'].replace('\n', '. ')):
            self.grant('listener')

    # ---------- dialogs ----------
    def open_help(self):
        HelpDialog(self).exec()
    def open_atlas(self):
        AtlasDialog(self).exec()
    def open_chronicle(self):
        ChronicleDialog(self).exec()
    def open_trial(self):
        TrialDialog(self).exec()
    def open_tonight(self):
        TonightDialog(self).exec()
    def open_finder(self):
        if not self.modal_open(): FinderDialog(self).exec()
    def open_achievements(self):
        AchievementsDialog(self).exec()
    def show_finale(self):
        FinaleDialog(self).exec()
    def open_wheel(self, id_):
        lv = next((x for x in LEVELS if x['id'] == id_), None)
        if lv: WheelDialog(self, lv).exec()
    def close_modals(self):
        for w in QApplication.topLevelWidgets():
            if isinstance(w, QDialog) and w.isVisible() and w is not self.title_dlg:
                w.close()
        self.tts.stop()
    def begin_anew(self):
        self.save = normalize_save({}); persist(self.save)
        self.apply_toggles(); self.upd_sky_label()
        self.toast('The atlas is blank again.')
        if hasattr(self, 'title_dlg'): self.title_dlg.refresh()
        self.show_title()

    # ---------- link hub ----------
    def handle_link(self, url):
        s = url.toString()
        if s.startswith('goto:'):
            self.close_modals(); self.load_level(int(s[5:]))
        elif s.startswith('study:'):
            i = int(s[6:]); self.close_modals()
            if self.unlocked(i): self.load_level(i, explore=True)
        elif s.startswith('next:'):
            i = int(s[5:]); self.close_modals()
            if i < len(LEVELS): self.load_level(i)
            else: self.show_finale()
        elif s.startswith('finish:'):
            self.close_modals(); self.show_finale()
        elif s.startswith('chgo:'):
            i = int(s[5:])
            if self.unlocked(i): self.close_modals(); self.load_level(i, explore=True)
        elif s.startswith('wheel:'):
            self.open_wheel(s[6:])
        elif s.startswith('seek:'):
            ra, dec, v = s[5:].split(',')
            self.sky.fly_to(float(ra), float(dec), float(v))
        elif s.startswith('tour:'):
            self.close_modals(); self.load_tour()

    # ---------- atlas codes ----------
    def export_code(self):
        import base64
        code = 'AST1.' + base64.b64encode(json.dumps(self.save).encode()).decode().rstrip('=')
        d = PanelDialog(self, 'the atlas, in code')
        d.body.setHtml(page(over('the atlas, in code') + h1('Carry your atlas elsewhere', sm=True) +
                            '<hr style="border:none;border-top:1px solid rgba(201,162,74,26%);">' +
                            tale_p('This line of letters is your whole atlas — plates, honours, best times. '
                                   'Copy it somewhere safe; paste it into another machine to continue there.') +
                            '<div style="font-family:\'IBM Plex Mono\',monospace;font-size:10.5px;'
                            'background:rgba(8,13,26,.7);border:1px solid rgba(201,162,74,26%);padding:10px;'
                            'user-select:text;word-break:break-all;user-select:text;">'+code+'</div>'))
        d.add_btn('Close', d.close, primary=True)
        QApplication.clipboard().setText(code)
        self.toast('The atlas code is copied to the clipboard.')
        d.exec()
    def import_code(self):
        d = PanelDialog(self, 'restore an atlas')
        d.body.setHtml(page(over('restore an atlas') + h1('Paste an atlas code', sm=True) +
                            '<hr style="border:none;border-top:1px solid rgba(201,162,74,26%);">' +
                            tale_p('Paste the code you carried with you. It will replace the atlas kept here.')))
        d.add_btn('Close', d.close, primary=True)
        d.exec()
        code, ok = QFileDialog.getOpenFileName  # placeholder to avoid unused warnings
        from PySide6.QtWidgets import QInputDialog
        text, ok = QInputDialog.getMultiLineText(self, 'Restore an atlas', 'Paste the AST1.… code here:')
        if not ok: return
        try:
            import base64
            raw = text.strip()
            assert raw.startswith('AST1.')
            b = raw[5:].replace('-', '+').replace('_', '/')
            b += '=' * (-len(b) % 4)
            v = normalize_save(json.loads(base64.b64decode(b).decode()))
        except Exception:
            self.toast('That code would not read — check that it is whole.'); return
        self.save = v; persist(self.save)
        self.apply_toggles(); self.upd_sky_label()
        self.toast('The atlas has been restored.')
        self.show_title()

    # ---------- keepsake ----------
    def take_poster(self):
        try:
            dpr = 2.0
            cols, gap, mar = 3, 18, 60
            cardW = (1240-mar*2-(cols-1)*gap)/cols; cardH = 226
            rows = math.ceil(len(LEVELS)/cols)
            Wp = 1240; Hp = int(mar*0.8+150+rows*(cardH+gap)+100)
            img = QImage(int(Wp*dpr), int(Hp*dpr), QImage.Format_ARGB32_Premultiplied)
            img.setDevicePixelRatio(dpr)
            p = QPainter(img); p.setRenderHint(QPainter.Antialiasing)
            p.setRenderHint(QPainter.SmoothPixmapTransform)
            p.fillRect(0, 0, Wp, Hp, QColor('#050a14'))
            p.setPen(QPen(QColor(201, 162, 74, 128), 1))
            p.drawLine(int(Wp/2-70), 40, int(Wp/2+70), 40)
            p.save(); p.translate(Wp/2, 40); p.rotate(45); p.drawRect(-4, -4, 8, 8); p.restore()
            f = QFont(); f.setFamilies(['Fraunces', 'Georgia', 'serif']); f.setPixelSize(46); f.setBold(True)
            f.setLetterSpacing(QFont.AbsoluteSpacing, 14)
            p.setFont(f); p.setPen(QColor('#f2e6c8'))
            p.drawText(QRectF(0, 50, Wp, 60), Qt.AlignCenter, 'ASTERISMA')
            f.setPixelSize(11); f.setBold(False); f.setLetterSpacing(QFont.AbsoluteSpacing, 6)
            p.setFont(f); p.setPen(QColor(201, 162, 74, 242))
            p.drawText(QRectF(0, 104, Wp, 20), Qt.AlignCenter, 'A FIELD ATLAS OF THE NIGHT')
            totS = sum(len([s for s in lv['stars'] if s['figure']]) for lv in LEVELS)
            totL = sum(len(lv['edges']) for lv in LEVELS)
            hon = sum(dd.get('stars', 0) for dd in self.save['done'].values())
            f.setPixelSize(15); f.setItalic(True); f.setLetterSpacing(QFont.AbsoluteSpacing, 1)
            f.setFamilies(['Fraunces', 'Georgia', 'serif'])
            p.setFont(f); p.setPen(QColor(231, 221, 196, 153))
            p.drawText(QRectF(0, 128, Wp, 22), Qt.AlignCenter,
                       '%s skies · %d stars · %d lines · %d of %d honours' %
                       (NUMWORD[len(LEVELS)], totS, totL, hon, len(LEVELS)*3))
            top = int(mar*0.8+150)
            for i, lv in enumerate(LEVELS):
                px = mar+(i % cols)*(cardW+gap); py = top+math.floor(i/cols)*(cardH+gap)
                draw_plate_into(p, lv, i+1, px, py, cardW, cardH-44)
                fo = QFont(); fo.setFamilies(['Fraunces', 'Georgia', 'serif']); fo.setPixelSize(15)
                p.setFont(fo); p.setPen(QColor('#e7ddc4'))
                p.drawText(QPointF(px+2, py+cardH-16), lv['name'])
                nw = p.fontMetrics().horizontalAdvance(lv['name'])
                fo.setItalic(True); fo.setPixelSize(12); p.setFont(fo)
                p.setPen(QColor(231, 221, 196, 128))
                p.drawText(QPointF(px+2+nw+8, py+cardH-16), lv['common'])
                fm = QFont(); fm.setFamilies(['IBM Plex Mono', 'monospace']); fm.setPixelSize(9)
                p.setFont(fm); p.setPen(QColor(201, 162, 74, 140))
                p.drawText(QPointF(px+cardW-26, py+cardH-16), rom(i+1))
            fy = Hp-74
            fo = QFont(); fo.setFamilies(['Fraunces', 'Georgia', 'serif']); fo.setItalic(True); fo.setPixelSize(14)
            p.setFont(fo); p.setPen(QColor(231, 221, 196, 191))
            p.drawText(QRectF(0, fy, Wp, 22), Qt.AlignCenter,
                       'Every figure here was first named by someone who needed the dark.')
            fm = QFont(); fm.setFamilies(['IBM Plex Mono', 'monospace']); fm.setPixelSize(9)
            p.setFont(fm); p.setPen(QColor(201, 162, 74, 128))
            p.drawText(QRectF(0, fy+26, Wp, 16), Qt.AlignCenter,
                       'CHARTED BY HAND IN ASTERISMA · '+time.strftime('%B %d, %Y'))
            p.end()
            path, _ = QFileDialog.getSaveFileName(self, 'Save the keepsake', 'asterisma-atlas.png',
                                                  'PNG image (*.png)')
            if path:
                img.save(path)
                self.grant('keepsake')
                self.toast('The atlas poster is saved.')
        except Exception:
            self.toast('The poster could not be saved here.')

    def paint_moon_btn(self):
        m = wanderers[0]
        pm = QPixmap(64, 64); pm.fill(Qt.transparent)
        p = QPainter(pm); p.setRenderHint(QPainter.Antialiasing)
        draw_moon_disc(p, 32, 32, 20, m['illum'], m['waxing'], True); p.end()
        self.moon_btn.setIcon(pm)
        self.moon_btn.setIconSize(pm.size().scaled(22, 22, Qt.KeepAspectRatio))
        self.moon_btn.setToolTip('Tonight’s sky — %s, %d%% lit (T)' % (m['phaseName'], round(m['illum']*100)))
        self.moon_btn.setFixedWidth(40)

    def escape(self):
        if self.sky.cfg.get('tour') and self.scene == 'game':
            self.show_title(); return
        self.sky.focus_star = None

    def resizeEvent(self, ev):
        super().resizeEvent(ev)
        if self.toast_lbl.isVisible():
            self.toast_lbl.move((self.sky.W-self.toast_lbl.width())//2,
                                self.sky.H-self.toast_lbl.height()-70)

    def closeEvent(self, ev):
        persist(self.save)
        try:
            if self.snd.ok: self.snd.sink.stop()
        except Exception:
            pass
        super().closeEvent(ev)

    def unlocked(self, i):
        return i == 0 or bool(self.save['done'].get(LEVELS[i-1]['id']))

# ============================== main ==============================
def main():
    app = QApplication(sys.argv)
    app.setStyle('Fusion')
    app.setStyleSheet(APP_CSS)
    w = Main()
    w.show()
    sys.exit(app.exec())

if __name__ == '__main__':
    main()