from __future__ import annotations
import argparse
import concurrent.futures
import hashlib
import math
import os
import re
import shutil
import stat
import struct
import subprocess
import sys
import threading
import time
import traceback
from dataclasses import dataclass, field
from pathlib import Path
from typing import Callable, Dict, Iterator, List, Optional, Sequence, Tuple

COMMENT_TEXT = "www.nostalgic.cc"
FLAC_LEVEL = "-8"
SOURCE_EXTENSIONS = (".m4a", ".alac")
WORK_DIR_PREFIX = ".alac2flac-work-"
MAX_INLINE_TAG_CHARS = 1000
MAX_COMMAND_LINE = 30000
FLAC_MAX_BLOCK = (1 << 24) - 1
DISK_MARGIN = 512 * 1024 * 1024

TEXT_ATOMS = {
    "\xa9nam": "TITLE",
    "\xa9ART": "ARTIST",
    "aART": "ALBUM ARTIST",
    "\xa9alb": "ALBUM",
    "\xa9day": "DATE",
    "\xa9gen": "GENRE",
    "\xa9wrt": "COMPOSER",
    "\xa9grp": "GROUPING",
    "\xa9lyr": "LYRICS",
    "cprt": "COPYRIGHT",
    "\xa9enc": "ENCODED BY",
    "\xa9wrk": "WORK",
    "\xa9mvn": "MOVEMENTNAME",
    "desc": "DESCRIPTION",
    "sonm": "TITLESORT",
    "soar": "ARTISTSORT",
    "soaa": "ALBUMARTISTSORT",
    "soal": "ALBUMSORT",
    "soco": "COMPOSERSORT",
}
INT_ATOMS = {
    "tmpo": "BPM",
    "\xa9mvi": "MOVEMENT",
    "\xa9mvc": "MOVEMENTTOTAL",
    "rtng": "ITUNESADVISORY",
}
FLAG_ATOMS = {
    "cpil": "COMPILATION",
    "shwm": "SHOWMOVEMENT",
}
IGNORED_ATOMS = {
    "\xa9too": "name of the program that made the ALAC file",
    "pgap": "iTunes gapless flag",
    "stik": "iTunes media kind",
    "hdvd": "iTunes HD video flag",
    "apID": "iTunes Store account e-mail",
    "ownr": "iTunes Store account owner",
    "purd": "iTunes Store purchase date",
    "cnID": "iTunes Store catalog ID",
    "atID": "iTunes Store artist ID",
    "plID": "iTunes Store playlist ID",
    "geID": "iTunes Store genre ID",
    "cmID": "iTunes Store composer ID",
    "sfID": "iTunes Store country code",
    "akID": "iTunes Store account type",
    "xid ": "iTunes Store vendor ID",
    "flvr": "iTunes Store file flavor",
    "pcst": "podcast flag",
    "purl": "podcast URL",
    "egid": "podcast episode ID",
    "catg": "podcast category",
    "keyw": "podcast keywords",
    "ldes": "long description (video)",
    "tvsh": "TV show name",
    "tven": "TV episode ID",
    "tvsn": "TV season",
    "tves": "TV episode",
    "tvnn": "TV network",
    "sosn": "TV show sort name",
}
FREEFORM_SKIP = {
    "itunnorm": "Apple Sound Check data",
    "itunsmpb": "AAC gapless (encoder delay) data",
    "itunes_cddb_ids": "iTunes CD lookup data",
    "itunes_cddb_1": "iTunes CD lookup data",
    "itunes_cddb_tracknumber": "iTunes CD lookup data",
    "itunmovi": "iTunes video data",
    "itunextc": "iTunes content rating",
    "encoding params": "binary encoder settings of the old file",
    "cdec": "name of the program that made the ALAC file",
}
FREEFORM_NAMES = {
    "musicbrainz track id": "MUSICBRAINZ_TRACKID",
    "musicbrainz release track id": "MUSICBRAINZ_RELEASETRACKID",
    "musicbrainz album id": "MUSICBRAINZ_ALBUMID",
    "musicbrainz artist id": "MUSICBRAINZ_ARTISTID",
    "musicbrainz album artist id": "MUSICBRAINZ_ALBUMARTISTID",
    "musicbrainz release group id": "MUSICBRAINZ_RELEASEGROUPID",
    "musicbrainz work id": "MUSICBRAINZ_WORKID",
    "musicbrainz disc id": "MUSICBRAINZ_DISCID",
    "musicbrainz original album id": "MUSICBRAINZ_ORIGINALALBUMID",
    "musicbrainz original artist id": "MUSICBRAINZ_ORIGINALARTISTID",
    "musicbrainz trm id": "MUSICBRAINZ_TRMID",
    "musicbrainz album type": "RELEASETYPE",
    "musicbrainz album status": "RELEASESTATUS",
    "musicbrainz album release country": "RELEASECOUNTRY",
    "musicip puid": "MUSICIP_PUID",
    "acoustid id": "ACOUSTID_ID",
    "acoustid fingerprint": "ACOUSTID_FINGERPRINT",
    "albumartist": "ALBUM ARTIST",
    "album_artist": "ALBUM ARTIST",
    "tracktotal": "TOTALTRACKS",
    "disctotal": "TOTALDISCS",
}
SINGLE_VALUE_FIELDS = ("TRACKNUMBER", "TOTALTRACKS", "DISCNUMBER", "TOTALDISCS")
FLAC_DEFAULT_MASKS = {
    1: (0x4, 0x1), 2: (0x3,), 3: (0x7,), 4: (0x33, 0x603), 5: (0x37, 0x607),
    6: (0x3F, 0x60F), 7: (0x70F,), 8: (0x63F,),
}
CHANNEL_MASK_TAG = "WAVEFORMATEXTENSIBLE_CHANNEL_MASK"
FIELD_ORDER = (
    "TITLE", "ARTIST", "ALBUM ARTIST", "ALBUM", "DATE", "GENRE", "COMPOSER",
    "PERFORMER", "TRACKNUMBER", "TOTALTRACKS", "DISCNUMBER", "TOTALDISCS", "COMMENT",
)

ID3_GENRES = (
    "Blues", "Classic Rock", "Country", "Dance", "Disco", "Funk", "Grunge", "Hip-Hop", "Jazz", "Metal",
    "New Age", "Oldies", "Other", "Pop", "R&B", "Rap", "Reggae", "Rock", "Techno", "Industrial",
    "Alternative", "Ska", "Death Metal", "Pranks", "Soundtrack", "Euro-Techno", "Ambient", "Trip-Hop", "Vocal", "Jazz+Funk",
    "Fusion", "Trance", "Classical", "Instrumental", "Acid", "House", "Game", "Sound Clip", "Gospel", "Noise",
    "Alternative Rock", "Bass", "Soul", "Punk", "Space", "Meditative", "Instrumental Pop", "Instrumental Rock", "Ethnic", "Gothic",
    "Darkwave", "Techno-Industrial", "Electronic", "Pop-Folk", "Eurodance", "Dream", "Southern Rock", "Comedy", "Cult", "Gangsta",
    "Top 40", "Christian Rap", "Pop/Funk", "Jungle", "Native American", "Cabaret", "New Wave", "Psychedelic", "Rave", "Showtunes",
    "Trailer", "Lo-Fi", "Tribal", "Acid Punk", "Acid Jazz", "Polka", "Retro", "Musical", "Rock & Roll", "Hard Rock",
    "Folk", "Folk-Rock", "National Folk", "Swing", "Fast Fusion", "Bebop", "Latin", "Revival", "Celtic", "Bluegrass",
    "Avantgarde", "Gothic Rock", "Progressive Rock", "Psychedelic Rock", "Symphonic Rock", "Slow Rock", "Big Band", "Chorus", "Easy Listening", "Acoustic",
    "Humour", "Speech", "Chanson", "Opera", "Chamber Music", "Sonata", "Symphony", "Booty Bass", "Primus", "Porn Groove",
    "Satire", "Slow Jam", "Club", "Tango", "Samba", "Folklore", "Ballad", "Power Ballad", "Rhythmic Soul", "Freestyle",
    "Duet", "Punk Rock", "Drum Solo", "A Cappella", "Euro-House", "Dance Hall", "Goa", "Drum & Bass", "Club-House", "Hardcore",
    "Terror", "Indie", "BritPop", "Afro-Punk", "Polsk Punk", "Beat", "Christian Gangsta Rap", "Heavy Metal", "Black Metal", "Crossover",
    "Contemporary Christian", "Christian Rock", "Merengue", "Salsa", "Thrash Metal", "Anime", "JPop", "Synthpop", "Abstract", "Art Rock",
    "Baroque", "Bhangra", "Big Beat", "Breakbeat", "Chillout", "Downtempo", "Dub", "EBM", "Eclectic", "Electro",
    "Electroclash", "Emo", "Experimental", "Garage", "Global", "IDM", "Illbient", "Industro-Goth", "Jam Band", "Krautrock",
    "Leftfield", "Lounge", "Math Rock", "New Romantic", "Nu-Breakz", "Post-Punk", "Post-Rock", "Psytrance", "Shoegaze", "Space Rock",
    "Trop Rock", "World Music", "Neoclassical", "Audiobook", "Audio Theatre", "Neue Deutsche Welle", "Podcast", "Indie Rock", "G-Funk", "Dubstep",
    "Garage Rock", "Psybient", "Hip-Hop / Rap", "Future Bass", "Dubstep", "Melodic Dubstep", "Trap",
)

PICTURE_TYPE_NAMES = {0: "other", 3: "front cover"}

_print_lock = threading.Lock()


def say(msg: str = "") -> None:
    with _print_lock:
        print(msg, flush=True)


def _setup_console() -> None:
    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(errors="replace")
        except (AttributeError, ValueError):
            pass


def _human_size(n: float) -> str:
    for unit in ("B", "KB", "MB", "GB"):
        if abs(n) < 1024 or unit == "GB":
            return ("%d %s" % (n, unit)) if unit == "B" else ("%.1f %s" % (n, unit))
        n /= 1024.0
    return "%.1f GB" % n


def _human_rate(hz: int) -> str:
    return "%g kHz" % (hz / 1000.0)


def _human_channels(n: int) -> str:
    return {1: "mono", 2: "stereo"}.get(n, "%d channels" % n)


def _human_duration(seconds: float) -> str:
    seconds = int(round(seconds))
    h, rest = divmod(seconds, 3600)
    m, s = divmod(rest, 60)
    return ("%d:%02d:%02d" % (h, m, s)) if h else ("%d:%02d" % (m, s))


def _natural_key(path: Path) -> list:
    return [int(t) if t.isdigit() else t for t in re.split(r"(\d+)", str(path).lower())]


def _tail(text: str, lines: int = 4, limit: int = 400) -> str:
    kept = [ln.strip() for ln in text.strip().splitlines() if ln.strip()][-lines:]
    out = " | ".join(kept)
    return out if len(out) <= limit else out[: limit - 3] + "..."


def _retry(fn: Callable, *args, attempts: int = 10, delay: float = 0.3):
    for attempt in range(attempts):
        try:
            return fn(*args)
        except PermissionError:
            if attempt == attempts - 1:
                raise
            time.sleep(delay)


def _remove_file(path: Path) -> None:
    try:
        _retry(os.remove, path)
    except FileNotFoundError:
        pass
    except PermissionError:
        os.chmod(path, stat.S_IWRITE)
        _retry(os.remove, path)


def _remove_tree(path: Path) -> bool:
    def on_error(func, p, _exc):
        try:
            os.chmod(p, stat.S_IWRITE)
            func(p)
        except OSError:
            pass
    for _ in range(10):
        if sys.version_info >= (3, 12):
            shutil.rmtree(path, onexc=on_error)
        else:
            shutil.rmtree(path, onerror=on_error)
        if not path.exists():
            return True
        time.sleep(0.3)
    return False

class Mp4Error(Exception):
    """The file is not a readable MP4/M4A container."""


class StepError(Exception):
    """A conversion step failed for one file."""


class Cancelled(Exception):
    """The user pressed Ctrl+C."""


@dataclass
class AudioTrack:
    codec: str
    audio_index: int
    timescale: int
    duration: Optional[int]
    bits: Optional[int] = None
    sample_rate: Optional[int] = None
    channels: Optional[int] = None
    entry_bits: Optional[int] = None
    entry_rate: Optional[int] = None
    entry_channels: Optional[int] = None


@dataclass
class Mp4File:
    tracks: List[AudioTrack]
    items: List[Tuple[str, List[Tuple[int, bytes]]]]
    truncated: bool
    problems: List[str]


@dataclass
class Picture:
    ptype: int
    mime: str
    data: bytes
    width: int
    height: int
    depth: int
    colors: int


@dataclass
class Job:
    index: int
    src: Path
    dst: Path
    rel: str
    bits: int
    sample_rate: int
    channels: int
    audio_index: int
    expected_samples: Optional[int]
    sample_tolerance: int
    tags: List[Tuple[str, str]]
    pictures: List[Picture]
    dropped: List[str]
    est_wav: int
    est_flac: int
    container_bits: int = 16
    blocking: List[str] = field(default_factory=list)
    notes: List[str] = field(default_factory=list)
    wav: Optional[Path] = None
    wav_md5: Optional[bytes] = None
    wav_samples: int = 0
    wav_bytes: int = 0
    channel_mask: Optional[int] = None
    flac_bytes: int = 0
    state: str = "planned"
    error: str = ""

    @property
    def fmt(self) -> str:
        return "%d-bit / %s / %s" % (self.bits, _human_rate(self.sample_rate), _human_channels(self.channels))


@dataclass
class Ctx:
    ffmpeg: Path
    flac: Path
    work: Path
    runner: "Runner"
    overwrite: bool
    verbose: bool

def _boxes(buf: bytes, start: int, end: int) -> Iterator[Tuple[bytes, int, int]]:
    pos = start
    while pos + 8 <= end:
        size, typ = struct.unpack_from(">I4s", buf, pos)
        header = 8
        if size == 1:
            if pos + 16 > end:
                raise Mp4Error("truncated box header")
            size = struct.unpack_from(">Q", buf, pos + 8)[0]
            header = 16
        elif size == 0:
            size = end - pos
        if size < header or pos + size > end:
            raise Mp4Error("damaged '%s' box" % typ.decode("latin-1"))
        yield typ, pos + header, pos + size
        pos += size


def _child(buf: bytes, start: int, end: int, want: bytes) -> Optional[Tuple[int, int]]:
    for typ, ps, pe in _boxes(buf, start, end):
        if typ == want:
            return ps, pe
    return None


def _path(buf: bytes, start: int, end: int, *types: bytes) -> Optional[Tuple[int, int]]:
    span: Optional[Tuple[int, int]] = (start, end)
    for typ in types:
        span = _child(buf, span[0], span[1], typ)
        if span is None:
            return None
    return span


def _meta_children_start(buf: bytes, start: int, end: int) -> int:
    if start + 8 <= end and buf[start + 4:start + 8] == b"hdlr":
        return start
    return start + 4


def _parse_sample_entry(buf: bytes, start: int, end: int, track: AudioTrack) -> None:
    if end - start >= 28:
        version = struct.unpack_from(">H", buf, start + 8)[0]
        track.entry_channels, track.entry_bits = struct.unpack_from(">HH", buf, start + 16)
        track.entry_rate = struct.unpack_from(">I", buf, start + 24)[0] >> 16
        if version == 2 and end - start >= 64:
            track.entry_rate = int(struct.unpack_from(">d", buf, start + 32)[0])
            track.entry_channels = struct.unpack_from(">I", buf, start + 40)[0]
    pos = buf.find(b"\x00\x00\x00\x24alac", start + 28, end)
    if pos >= 0 and pos + 36 <= end:
        (_frame_len, _compat, bits, _pb, _mb, _kb, channels, _max_run,
         _max_frame, _avg_rate, rate) = struct.unpack_from(">IBBBBBBHIII", buf, pos + 12)
        track.bits, track.channels, track.sample_rate = bits, channels, rate


def _parse_trak(buf: bytes, start: int, end: int, audio_index: int) -> Optional[AudioTrack]:
    mdia = _child(buf, start, end, b"mdia")
    if mdia is None:
        return None
    hdlr = _child(buf, mdia[0], mdia[1], b"hdlr")
    if hdlr is None or hdlr[1] - hdlr[0] < 12 or buf[hdlr[0] + 8:hdlr[0] + 12] != b"soun":
        return None
    timescale, duration = 0, None
    mdhd = _child(buf, mdia[0], mdia[1], b"mdhd")
    if mdhd is not None:
        s = mdhd[0]
        if buf[s] == 1 and mdhd[1] - s >= 32:
            timescale, duration = struct.unpack_from(">IQ", buf, s + 20)
        elif mdhd[1] - s >= 20:
            timescale, duration = struct.unpack_from(">II", buf, s + 12)
    track = AudioTrack(codec="?", audio_index=audio_index, timescale=timescale, duration=duration)
    stbl = _path(buf, mdia[0], mdia[1], b"minf", b"stbl")
    if stbl is None:
        return track
    stsd = _child(buf, stbl[0], stbl[1], b"stsd")
    if stsd is not None and stsd[1] - stsd[0] >= 16:
        entry_size, entry_type = struct.unpack_from(">I4s", buf, stsd[0] + 8)
        track.codec = entry_type.decode("latin-1")
        entry_end = min(stsd[0] + 8 + entry_size, stsd[1])
        _parse_sample_entry(buf, stsd[0] + 16, entry_end, track)
    stts = _child(buf, stbl[0], stbl[1], b"stts")
    if stts is not None and stts[1] - stts[0] >= 8:
        count = struct.unpack_from(">I", buf, stts[0] + 4)[0]
        if stts[0] + 8 + count * 8 <= stts[1]:
            total = 0
            for i in range(count):
                n, delta = struct.unpack_from(">II", buf, stts[0] + 8 + i * 8)
                total += n * delta
            track.duration = total
    return track


def _parse_ilst(buf: bytes, start: int, end: int, problems: List[str]) -> List[Tuple[str, List[Tuple[int, bytes]]]]:
    items: List[Tuple[str, List[Tuple[int, bytes]]]] = []
    try:
        for typ, ps, pe in _boxes(buf, start, end):
            key = typ.decode("latin-1")
            mean = name = None
            values: List[Tuple[int, bytes]] = []
            try:
                for ctyp, cps, cpe in _boxes(buf, ps, pe):
                    if ctyp == b"mean" and cpe - cps >= 4:
                        mean = buf[cps + 4:cpe].decode("utf-8", "replace").strip("\x00")
                    elif ctyp == b"name" and cpe - cps >= 4:
                        name = buf[cps + 4:cpe].decode("utf-8", "replace").strip("\x00")
                    elif ctyp == b"data" and cpe - cps >= 8:
                        dtype = int.from_bytes(buf[cps + 1:cps + 4], "big")
                        values.append((dtype, bytes(buf[cps + 8:cpe])))
            except Mp4Error as exc:
                problems.append("tag '%s' is damaged (%s)" % (key, exc))
            if typ == b"----":
                if not name:
                    problems.append("a custom tag without a name was skipped")
                    continue
                key = "----:%s:%s" % (mean or "", name)
            items.append((key, values))
    except Mp4Error as exc:
        problems.append("the tag list is damaged (%s)" % exc)
    return items


def parse_mp4(path: Path) -> Mp4File:
    problems: List[str] = []
    truncated = False
    with open(path, "rb") as f:
        size = os.fstat(f.fileno()).st_size
        head = f.read(12)
        if head[:4] == b"caff":
            raise Mp4Error("this is a CAF file, not an MP4/M4A file")
        if len(head) < 12 or head[4:8] not in (b"ftyp", b"moov", b"mdat", b"free", b"skip", b"wide", b"uuid", b"pnot", b"junk"):
            raise Mp4Error("not an MP4/M4A file")
        moov = None
        pos = 0
        while pos + 8 <= size:
            f.seek(pos)
            hdr = f.read(16)
            if len(hdr) < 8:
                break
            box_size, typ = struct.unpack_from(">I4s", hdr)
            header = 8
            if box_size == 1:
                if len(hdr) < 16:
                    break
                box_size = struct.unpack_from(">Q", hdr, 8)[0]
                header = 16
            elif box_size == 0:
                box_size = size - pos
            if box_size < header:
                raise Mp4Error("damaged '%s' box at offset %d" % (typ.decode("latin-1"), pos))
            if pos + box_size > size:
                truncated = True
                box_size = size - pos
            if typ == b"moov" and moov is None:
                moov = (pos + header, pos + box_size)
            pos += box_size
        if moov is None:
            raise Mp4Error("no 'moov' box")
        f.seek(moov[0])
        buf = f.read(moov[1] - moov[0])
    if truncated:
        problems.append("the file appears to be corrupt")

    end = len(buf)
    tracks: List[AudioTrack] = []
    items: List[Tuple[str, List[Tuple[int, bytes]]]] = []
    try:
        audio_index = 0
        for typ, ps, pe in _boxes(buf, 0, end):
            if typ == b"trak":
                track = _parse_trak(buf, ps, pe, audio_index)
                if track is not None:
                    tracks.append(track)
                    audio_index += 1
            elif typ in (b"udta", b"meta") and not items:
                if typ == b"udta":
                    meta = _child(buf, ps, pe, b"meta")
                else:
                    meta = (ps, pe)
                if meta is not None:
                    ilst = _child(buf, _meta_children_start(buf, meta[0], meta[1]), meta[1], b"ilst")
                    if ilst is not None:
                        items = _parse_ilst(buf, ilst[0], ilst[1], problems)
    except Mp4Error as exc:
        if not tracks:
            raise
        problems.append("part of the file header is damaged (%s)" % exc)
    return Mp4File(tracks=tracks, items=items, truncated=truncated, problems=problems)

def _decode_text(dtype: int, payload: bytes) -> Optional[str]:
    if dtype in (1, 4):
        return payload.decode("utf-8", "replace")
    if dtype in (2, 5):
        return payload.decode("utf-16-be", "replace")
    if dtype == 3:
        return payload.decode("shift_jis", "replace")
    if dtype == 0:
        try:
            text = payload.decode("utf-8")
        except UnicodeDecodeError:
            return None
        if any(ord(c) < 32 and c not in "\t\r\n\x00" for c in text):
            return None
        return text
    if dtype in (21, 22, 65, 66, 67, 74, 75, 76, 77, 78):
        number = _decode_int(dtype, payload)
        return None if number is None else str(number)
    return None


def _decode_int(dtype: int, payload: bytes) -> Optional[int]:
    if not payload or len(payload) > 8:
        return None
    if dtype in (21, 0, 65, 66, 67, 74):
        return int.from_bytes(payload, "big", signed=True)
    if dtype in (22, 75, 76, 77, 78):
        return int.from_bytes(payload, "big", signed=False)
    if dtype in (1, 4):
        text = payload.decode("utf-8", "replace").strip("\x00 ")
        return int(text) if re.fullmatch(r"-?\d+", text) else None
    return None


def _clean_values(text: str) -> List[str]:
    return [part for part in text.split("\x00") if part.strip()]


def _number_pair(values: List[Tuple[int, bytes]]) -> Tuple[Optional[int], Optional[int]]:
    for dtype, payload in values:
        if dtype in (1, 4):
            m = re.match(r"\s*(\d+)\s*(?:/\s*(\d+))?", payload.decode("utf-8", "replace"))
            if m:
                return int(m.group(1)) or None, (int(m.group(2)) if m.group(2) else 0) or None
        elif len(payload) >= 4:
            number = int.from_bytes(payload[2:4], "big")
            total = int.from_bytes(payload[4:6], "big") if len(payload) >= 6 else 0
            return number or None, total or None
    return None, None


def vorbis_field_name(name: str) -> str:
    clean = "".join(c if 0x20 <= ord(c) <= 0x7D and c != "=" else "_" for c in name)
    return clean.strip().upper()


def _image_info(data: bytes) -> Optional[Tuple[str, int, int, int, int]]:
    try:
        if data[:3] == b"\xff\xd8\xff":
            i = 2
            while i + 4 <= len(data):
                if data[i] != 0xFF:
                    i += 1
                    continue
                marker = data[i + 1]
                if marker == 0xFF:
                    i += 1
                    continue
                if marker in (0xD8, 0x01) or 0xD0 <= marker <= 0xD7:
                    i += 2
                    continue
                if marker in (0xD9, 0xDA):
                    break
                seg_len = struct.unpack_from(">H", data, i + 2)[0]
                if marker in (0xC0, 0xC1, 0xC2, 0xC3, 0xC5, 0xC6, 0xC7, 0xC9, 0xCA, 0xCB, 0xCD, 0xCE, 0xCF):
                    precision = data[i + 4]
                    height, width = struct.unpack_from(">HH", data, i + 5)
                    components = data[i + 9]
                    if width and height:
                        return "image/jpeg", width, height, precision * components, 0
                    return None
                i += 2 + seg_len
            return None
        if data[:8] == b"\x89PNG\r\n\x1a\n" and data[12:16] == b"IHDR":
            width, height, bit_depth, color_type = struct.unpack_from(">IIBB", data, 16)
            colors = 0
            if color_type == 3:
                depth = 24
                pos = 8
                while pos + 8 <= len(data):
                    length, ctype = struct.unpack_from(">I4s", data, pos)
                    if ctype == b"PLTE":
                        colors = length // 3
                        break
                    if ctype == b"IDAT":
                        break
                    pos += 12 + length
            else:
                depth = bit_depth * {0: 1, 2: 3, 4: 2, 6: 4}.get(color_type, 1)
            return "image/png", width, height, depth, colors
        if data[:6] in (b"GIF87a", b"GIF89a") and len(data) >= 13:
            width, height, packed = struct.unpack_from("<HHB", data, 6)
            colors = (1 << ((packed & 0x07) + 1)) if packed & 0x80 else 0
            return "image/gif", width, height, 24, colors
        if data[:2] == b"BM" and len(data) >= 30:
            header_size = struct.unpack_from("<I", data, 14)[0]
            if header_size == 12:
                width, height, _planes, bpp = struct.unpack_from("<HHHH", data, 18)
                used = 0
            else:
                width, height, _planes, bpp = struct.unpack_from("<iiHH", data, 18)
                used = struct.unpack_from("<I", data, 46)[0] if len(data) >= 50 else 0
            colors = (used or (1 << bpp)) if bpp <= 8 else 0
            return "image/bmp", abs(width), abs(height), bpp, colors
        if data[:4] == b"RIFF" and data[8:12] == b"WEBP" and len(data) >= 30:
            chunk = data[12:16]
            if chunk == b"VP8 ":
                width, height = struct.unpack_from("<HH", data, 26)
                return "image/webp", width & 0x3FFF, height & 0x3FFF, 24, 0
            if chunk == b"VP8L":
                bits = struct.unpack_from("<I", data, 21)[0]
                alpha = (bits >> 28) & 1
                return "image/webp", (bits & 0x3FFF) + 1, ((bits >> 14) & 0x3FFF) + 1, 32 if alpha else 24, 0
            if chunk == b"VP8X":
                alpha = data[20] & 0x10
                width = int.from_bytes(data[24:27], "little") + 1
                height = int.from_bytes(data[27:30], "little") + 1
                return "image/webp", width, height, 32 if alpha else 24, 0
    except (struct.error, IndexError):
        return None
    return None


def build_tags(items: List[Tuple[str, List[Tuple[int, bytes]]]]) -> Tuple[List[Tuple[str, str]], List[Picture], List[str], List[str]]:
    tags: List[Tuple[str, str]] = []
    pictures: List[Picture] = []
    dropped: List[str] = []
    problems: List[str] = []
    have_text_genre = any(key == "\xa9gen" for key, _ in items)

    def add(name: str, value: str) -> None:
        for v in _clean_values(value):
            tags.append((name, v))

    for key, values in sorted(items, key=lambda item: item[0].startswith("----:")):
        if key in TEXT_ATOMS:
            for dtype, payload in values:
                text = _decode_text(dtype, payload)
                if text is not None:
                    add(TEXT_ATOMS[key], text)
        elif key == "\xa9cmt":
            dropped.append("%s (comment; replaced with %s)" % (key, COMMENT_TEXT))
        elif key == "trkn":
            number, total = _number_pair(values)
            if number:
                tags.append(("TRACKNUMBER", str(number)))
            if total:
                tags.append(("TOTALTRACKS", str(total)))
        elif key == "disk":
            number, total = _number_pair(values)
            if number:
                tags.append(("DISCNUMBER", str(number)))
            if total:
                tags.append(("TOTALDISCS", str(total)))
        elif key == "gnre":
            if have_text_genre:
                continue
            for dtype, payload in values:
                number = int.from_bytes(payload[:2], "big") if payload else 0
                if 1 <= number <= len(ID3_GENRES):
                    tags.append(("GENRE", ID3_GENRES[number - 1]))
        elif key in INT_ATOMS or key in FLAG_ATOMS:
            for dtype, payload in values:
                number = _decode_int(dtype, payload)
                if number:
                    tags.append((INT_ATOMS[key], str(number)) if key in INT_ATOMS else (FLAG_ATOMS[key], "1"))
        elif key == "covr":
            for n, (dtype, payload) in enumerate(values):
                info = _image_info(payload)
                if info is None:
                    problems.append("cover image #%d is not a readable JPEG/PNG/GIF/BMP/WebP image" % (n + 1))
                    continue
                mime, width, height, depth, colors = info
                if len(payload) + len(mime) + 32 > FLAC_MAX_BLOCK:
                    problems.append("cover image #%d is larger than the 16 MB FLAC limit" % (n + 1))
                    continue
                ptype = 3 if not pictures else 0
                pictures.append(Picture(ptype, mime, payload, width, height, depth, colors))
        elif key.startswith("----:"):
            _, _mean, name = key.split(":", 2)
            lname = name.strip().lower()
            if lname in FREEFORM_SKIP:
                dropped.append("%s (%s)" % (name, FREEFORM_SKIP[lname]))
                continue
            vname = FREEFORM_NAMES.get(lname) or vorbis_field_name(name)
            if not vname:
                dropped.append("%s (Name cannot be used as a FLAC field)" % name)
                continue
            if vname == "COMMENT":
                dropped.append("%s (Replaced with %s)" % (name, COMMENT_TEXT))
                continue
            kept = False
            for dtype, payload in values:
                text = _decode_text(dtype, payload)
                if text is not None:
                    add(vname, text)
                    kept = True
            if values and not kept:
                dropped.append("%s (binary data)" % name)
        elif key in IGNORED_ATOMS:
            dropped.append("%s (%s)" % (key, IGNORED_ATOMS[key]))
        else:
            dropped.append("%s (no FLAC equivalent)" % key)

    tags.append(("COMMENT", COMMENT_TEXT))
    seen = set()
    seen_single = set()
    unique: List[Tuple[str, str]] = []
    for name, value in tags:
        if (name, value) in seen:
            continue
        if name in SINGLE_VALUE_FIELDS or name == "COMMENT":
            if name in seen_single:
                continue
            seen_single.add(name)
        seen.add((name, value))
        unique.append((name, value))

    def order(item: Tuple[int, Tuple[str, str]]) -> Tuple[int, int]:
        pos, (name, _value) = item
        if name in FIELD_ORDER:
            return FIELD_ORDER.index(name), pos
        if name.startswith("REPLAYGAIN_"):
            return len(FIELD_ORDER) + 1, pos
        return len(FIELD_ORDER), pos

    ordered = [tag for _, tag in sorted(enumerate(unique), key=order)]
    return ordered, pictures, dropped, problems

@dataclass
class WavInfo:
    channels: int
    sample_rate: int
    bits: int
    valid_bits: int
    block_align: int
    data_offset: int
    data_size: int
    valid_bits_offset: Optional[int]
    channel_mask: Optional[int]


def read_wav_info(path: Path) -> WavInfo:
    size = path.stat().st_size
    with open(path, "rb") as f:
        head = f.read(12)
        if len(head) < 12 or head[:4] not in (b"RIFF", b"RF64") or head[8:12] != b"WAVE":
            raise StepError("ffmpeg did not produce a valid WAV file")
        ds64_size = None
        fmt = None
        pos = 12
        while pos + 8 <= size:
            f.seek(pos)
            cid, csize = struct.unpack("<4sI", f.read(8))
            body = pos + 8
            if cid == b"ds64":
                ds64_size = struct.unpack_from("<Q", f.read(16), 8)[0]
            elif cid == b"fmt ":
                raw = f.read(csize)
                tag, channels, rate, _byte_rate, block_align, bits = struct.unpack_from("<HHIIHH", raw)
                valid, valid_off, mask = bits, None, None
                if tag == 0xFFFE and len(raw) >= 40:
                    valid = struct.unpack_from("<H", raw, 18)[0] or bits
                    valid_off = body + 18
                    mask = struct.unpack_from("<I", raw, 20)[0]
                    tag = struct.unpack_from("<H", raw, 24)[0]
                if tag != 1:
                    raise StepError("ffmpeg wrote a non-PCM WAV (format tag %#x)" % tag)
                fmt = (channels, rate, bits, valid, block_align, valid_off, mask)
            elif cid == b"data":
                if fmt is None:
                    raise StepError("WAV has no format chunk")
                data_size = ds64_size if (head[:4] == b"RF64" and ds64_size is not None) else csize
                if body + data_size > size:
                    raise StepError("WAV data is shorter than its header says")
                channels, rate, bits, valid, block_align, valid_off, mask = fmt
                return WavInfo(channels, rate, bits, valid, block_align, body, data_size, valid_off, mask)
            pos = body + csize + (csize & 1)
    raise StepError("WAV has no data chunk")


def md5_of_range(path: Path, offset: int, length: int) -> bytes:
    digest = hashlib.md5()
    with open(path, "rb") as f:
        f.seek(offset)
        remaining = length
        while remaining > 0:
            chunk = f.read(min(remaining, 4 << 20))
            if not chunk:
                raise StepError("WAV ended early while checking it")
            digest.update(chunk)
            remaining -= len(chunk)
    return digest.digest()


@dataclass
class FlacInfo:
    sample_rate: int
    channels: int
    bits: int
    total_samples: int
    md5: bytes
    comments: List[Tuple[str, str]]
    pictures: List[Tuple[int, str, bytes]]


def read_flac_info(path: Path) -> FlacInfo:
    info = None
    comments: List[Tuple[str, str]] = []
    pictures: List[Tuple[int, str, bytes]] = []
    with open(path, "rb") as f:
        if f.read(4) != b"fLaC":
            raise StepError("Output is not a FLAC file")
        while True:
            header = f.read(4)
            if len(header) < 4:
                raise StepError("FLAC metadata is cut short")
            last, btype = header[0] & 0x80, header[0] & 0x7F
            body = f.read(int.from_bytes(header[1:4], "big"))
            if btype == 0:
                packed = int.from_bytes(body[10:18], "big")
                info = (packed >> 44, ((packed >> 41) & 7) + 1, ((packed >> 36) & 31) + 1,
                        packed & ((1 << 36) - 1), body[18:34])
            elif btype == 4:
                vendor_len = struct.unpack_from("<I", body)[0]
                pos = 4 + vendor_len
                count = struct.unpack_from("<I", body, pos)[0]
                pos += 4
                for _ in range(count):
                    length = struct.unpack_from("<I", body, pos)[0]
                    entry = body[pos + 4:pos + 4 + length].decode("utf-8", "replace")
                    pos += 4 + length
                    name, _, value = entry.partition("=")
                    comments.append((name, value))
            elif btype == 6:
                ptype, mime_len = struct.unpack_from(">II", body)
                mime = body[8:8 + mime_len].decode("ascii", "replace")
                pos = 8 + mime_len
                desc_len = struct.unpack_from(">I", body, pos)[0]
                pos += 4 + desc_len + 16
                data_len = struct.unpack_from(">I", body, pos)[0]
                pictures.append((ptype, mime, body[pos + 4:pos + 4 + data_len]))
            if last:
                break
    if info is None:
        raise StepError("FLAC has no STREAMINFO block")
    return FlacInfo(info[0], info[1], info[2], info[3], info[4], comments, pictures)

def _script_dir() -> Path:
    if getattr(sys, "frozen", False):
        return Path(sys.executable).resolve().parent
    return Path(os.path.abspath(__file__)).resolve().parent


def find_tool(name: str, folders: Sequence[Path]) -> Optional[Path]:
    exe = name + ".exe" if os.name == "nt" else name
    for folder in folders:
        candidate = folder / exe
        if candidate.is_file():
            return candidate
    found = shutil.which(name)
    return Path(found).resolve() if found else None


def tool_version(path: Path, arg: str) -> Optional[str]:
    try:
        result = subprocess.run([str(path), arg], stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, timeout=60)
    except (OSError, subprocess.SubprocessError):
        return None
    if result.returncode != 0:
        return None
    lines = result.stdout.decode("utf-8", "replace").strip().splitlines()
    return lines[0].strip() if lines else ""


class Runner:

    def __init__(self) -> None:
        self.cancelled = threading.Event()
        self._procs: set = set()
        self._lock = threading.Lock()

    def run(self, cmd: List[str]) -> Tuple[int, str]:
        if self.cancelled.is_set():
            raise Cancelled()
        proc = subprocess.Popen(cmd, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        with self._lock:
            self._procs.add(proc)
        try:
            out, err = proc.communicate()
        finally:
            with self._lock:
                self._procs.discard(proc)
        if self.cancelled.is_set():
            raise Cancelled()
        text = (err or b"").decode("utf-8", "replace")
        if out:
            text = out.decode("utf-8", "replace") + text
        return proc.returncode, text

    def cancel(self) -> None:
        self.cancelled.set()
        with self._lock:
            for proc in list(self._procs):
                try:
                    proc.kill()
                except OSError:
                    pass

def find_sources(folder: Path, recursive: bool) -> List[Path]:
    found = []
    candidates = folder.rglob("*") if recursive else folder.iterdir()
    for path in candidates:
        rel_parts = path.relative_to(folder).parts
        if any(part.startswith(WORK_DIR_PREFIX) for part in rel_parts):
            continue
        if path.name.startswith("._"):
            continue
        if path.suffix.lower() in SOURCE_EXTENSIONS and path.is_file():
            found.append(path)
    return sorted(found, key=_natural_key)


def plan_job(index: int, src: Path, folder: Path, flac_version: Tuple[int, ...]) -> Job:
    try:
        mp4 = parse_mp4(src)
    except Mp4Error as exc:
        raise StepError(str(exc))
    except OSError as exc:
        raise StepError("cannot read the file (%s)" % exc.strerror)
    if not mp4.tracks:
        raise StepError("the file has no audio track")
    track = next((t for t in mp4.tracks if t.codec == "alac"), None)
    if track is None:
        codec = mp4.tracks[0].codec
        if codec == "mp4a":
            raise StepError("this is AAC, not ALAC.")
        raise StepError("the audio is '%s', not ALAC" % codec)
    bits = track.bits or track.entry_bits
    rate = track.sample_rate or track.entry_rate
    channels = track.channels or track.entry_channels
    if not bits or not rate or not channels:
        raise StepError("cannot find the ALAC bit depth / sample rate / channel count")
    if not 4 <= bits <= 32:
        raise StepError("unsupported bit depth (%d)" % bits)
    if channels > 8:
        raise StepError("FLAC supports at most 8 channels (this file has %d)" % channels)
    if bits > 24 and flac_version < (1, 4):
        raise StepError("%d-bit audio needs flac 1.4.0 or newer" % bits)

    expected, tolerance = None, 0
    if track.duration and track.timescale:
        if track.timescale == rate:
            expected = track.duration
        else:
            expected = int(round(track.duration * rate / track.timescale))
            tolerance = int(math.ceil(rate / track.timescale)) + 1

    tags, pictures, dropped, tag_problems = build_tags(mp4.items)
    container = 16 if bits <= 16 else 24 if bits <= 24 else 32
    samples_estimate = expected if expected else int(src.stat().st_size * 8 // (bits * channels)) * 2
    est_wav = samples_estimate * channels * (container // 8) + 4096
    est_flac = int(src.stat().st_size * 1.1) + sum(len(p.data) for p in pictures)
    job = Job(
        index=index, src=src, dst=src.with_suffix(".flac"), rel=str(src.relative_to(folder)),
        bits=bits, sample_rate=rate, channels=channels, audio_index=track.audio_index,
        expected_samples=expected, sample_tolerance=tolerance, tags=tags, pictures=pictures,
        dropped=dropped, est_wav=est_wav, est_flac=est_flac, container_bits=container,
    )
    job.blocking.extend(mp4.problems)
    job.blocking.extend(tag_problems)
    if len(mp4.tracks) > 1:
        job.blocking.append("The file has %d audio tracks. Only first track converted."
                            % len(mp4.tracks))
    return job


def describe_job(job: Job) -> None:
    length = ""
    if job.expected_samples:
        length = ", %s" % _human_duration(job.expected_samples / job.sample_rate)
    say("  %s" % job.rel)
    say("      ALAC %s%s" % (job.fmt, length))
    for name, value in job.tags:
        shown = value.replace("\r", "").replace("\n", " / ")
        if len(shown) > 90:
            shown = shown[:87] + "..."
        say("      %s=%s" % (name, shown))
    for pic in job.pictures:
        say("      [picture] %s, %s %dx%d, %s" % (PICTURE_TYPE_NAMES.get(pic.ptype, pic.ptype), pic.mime,
                                                 pic.width, pic.height, _human_size(len(pic.data))))
    for item in job.dropped:
        say("      [not copied] %s" % item)
    for problem in job.blocking:
        say("      [warning] %s" % problem)
    for note in job.notes:
        say("      [note] %s" % note)


def plan_batches(jobs: List[Job], free: int) -> List[List[Job]]:
    flac_total = sum(j.est_flac for j in jobs)
    wav_total = sum(j.est_wav for j in jobs)
    if wav_total + flac_total + DISK_MARGIN <= free:
        return [jobs]
    budget = free - DISK_MARGIN - flac_total
    largest = max(j.est_wav for j in jobs)
    if budget < largest:
        raise StepError("not enough free disk space: about %s is needed, %s is free"
                        % (_human_size(largest + flac_total + DISK_MARGIN), _human_size(free)))
    batches: List[List[Job]] = []
    current: List[Job] = []
    used = 0
    for job in jobs:
        if current and used + job.est_wav > budget:
            batches.append(current)
            current, used = [], 0
        current.append(job)
        used += job.est_wav
    if current:
        batches.append(current)
    return batches

def decode_to_wav(job: Job, ctx: Ctx) -> str:
    wav = ctx.work / ("%04d.wav" % job.index)
    codec = "pcm_s%dle" % job.container_bits
    if job.est_wav > 0xFFFFFFFF - (16 << 20):
        rf64 = "always"
    else:
        rf64 = "never" if job.expected_samples else "auto"
    cmd = [
        str(ctx.ffmpeg), "-hide_banner", "-nostdin", "-v", "error", "-xerror",
        "-ignore_editlist", "1",
        "-i", str(job.src),
        "-map", "0:a:%d" % job.audio_index,
        "-map_metadata", "-1", "-map_chapters", "-1",
        "-c:a", codec, "-fflags", "+bitexact", "-flags:a", "+bitexact",
        "-rf64", rf64, "-f", "wav", "-y", str(wav),
    ]
    job.wav = wav
    rc, err = ctx.runner.run(cmd)
    if rc != 0:
        raise StepError("ffmpeg failed: %s" % (_tail(err) or "exit code %d" % rc))
    if err.strip():
        job.blocking.append("ffmpeg reported: %s" % _tail(err))

    info = read_wav_info(wav)
    if info.channels != job.channels:
        raise StepError("ffmpeg decoded %d channels, the file says %d" % (info.channels, job.channels))
    if info.sample_rate != job.sample_rate:
        raise StepError("ffmpeg decoded at %d Hz, the file says %d Hz" % (info.sample_rate, job.sample_rate))
    if info.bits != job.container_bits:
        raise StepError("ffmpeg wrote %d-bit samples, expected %d-bit" % (info.bits, job.container_bits))
    if job.bits != info.valid_bits:
        if info.valid_bits_offset is None:
            raise StepError("cannot mark %d-bit audio in a %d-bit WAV" % (job.bits, info.bits))
        with open(wav, "r+b") as f:
            f.seek(info.valid_bits_offset)
            f.write(struct.pack("<H", job.bits))
        info.valid_bits = job.bits

    if info.data_size % info.block_align:
        job.blocking.append("WAV data ends with a partial sample frame")
    job.wav_samples = info.data_size // info.block_align
    job.wav_bytes = info.data_size
    job.channel_mask = info.channel_mask
    if info.channel_mask and info.channel_mask in FLAC_DEFAULT_MASKS.get(info.channels, ()):
        with open(wav, "r+b") as f:
            f.seek(info.valid_bits_offset + 2)
            f.write(struct.pack("<I", 0))
        job.channel_mask = None
    if job.expected_samples is not None and abs(job.wav_samples - job.expected_samples) > job.sample_tolerance:
        job.blocking.append("decoded %d samples but the file's index lists %d"
                            % (job.wav_samples, job.expected_samples))
    if info.valid_bits == info.bits:
        job.wav_md5 = md5_of_range(wav, info.data_offset, info.data_size)
    job.state = "decoded"
    return "WAV ready (%s)" % job.fmt


def _flac_command(job: Job, ctx: Ctx, out: Path, all_tags_in_files: bool) -> List[str]:
    cmd = [str(ctx.flac), FLAC_LEVEL, "--verify", "--silent", "--force", "--no-utf8-convert",
           "--output-name=%s" % out]
    if job.sample_rate > 655350 or (job.sample_rate > 65535 and job.sample_rate % 10):
        cmd.append("--lax")
    for n, (name, value) in enumerate(job.tags):
        if all_tags_in_files or len(value) > MAX_INLINE_TAG_CHARS or "\n" in value or "\r" in value:
            tag_file = ctx.work / ("%04d_tag%03d.txt" % (job.index, n))
            tag_file.write_bytes(value.encode("utf-8"))
            cmd.append("--tag-from-file=%s=%s" % (name, tag_file))
        else:
            cmd.append("--tag=%s=%s" % (name, value))
    for n, pic in enumerate(job.pictures):
        pic_file = ctx.work / ("%04d_pic%02d.img" % (job.index, n))
        pic_file.write_bytes(pic.data)
        dims = "%dx%dx%d" % (pic.width, pic.height, pic.depth)
        if pic.colors:
            dims += "/%d" % pic.colors
        cmd.append("--picture=%d|%s||%s|%s" % (pic.ptype, pic.mime, dims, pic_file))
    cmd.append(str(job.wav))
    return cmd


def encode_to_flac(job: Job, ctx: Ctx) -> str:
    out = ctx.work / ("%04d.flac" % job.index)
    cmd = _flac_command(job, ctx, out, all_tags_in_files=False)
    if len(subprocess.list2cmdline(cmd)) > MAX_COMMAND_LINE:
        cmd = _flac_command(job, ctx, out, all_tags_in_files=True)
    rc, err = ctx.runner.run(cmd)
    if rc != 0:
        raise StepError("flac failed: %s" % (_tail(err) or "exit code %d" % rc))
    if err.strip():
        job.notes.append("flac said: %s" % _tail(err))

    rc, err = ctx.runner.run([str(ctx.flac), "--test", "--silent", str(out)])
    if rc != 0:
        raise StepError("the new FLAC failed flac --test: %s" % (_tail(err) or "exit code %d" % rc))

    info = read_flac_info(out)
    problems = []
    if info.sample_rate != job.sample_rate:
        problems.append("sample rate %d instead of %d" % (info.sample_rate, job.sample_rate))
    if info.channels != job.channels:
        problems.append("%d channels instead of %d" % (info.channels, job.channels))
    if info.bits != job.bits:
        problems.append("%d-bit instead of %d-bit" % (info.bits, job.bits))
    if info.total_samples != job.wav_samples:
        problems.append("%d samples instead of %d" % (info.total_samples, job.wav_samples))
    if job.wav_md5 is not None and info.md5 != job.wav_md5:
        problems.append("audio MD5 does not match the decoded ALAC")
    comments = [(name, value) for name, value in info.comments
                if not (name.upper() == CHANNEL_MASK_TAG and job.channel_mask
                        and re.fullmatch(r"0x[0-9A-Fa-f]+", value) and int(value, 16) == job.channel_mask)]
    if sorted(comments) != sorted(job.tags):
        missing = [t for t in job.tags if t not in comments]
        extra = [t for t in comments if t not in job.tags]
        problems.append("tags differ (missing %s, unexpected %s)" % (missing[:3], extra[:3]))
    if [(p[0], p[2]) for p in info.pictures] != [(p.ptype, p.data) for p in job.pictures]:
        problems.append("embedded pictures differ from source")
    if problems:
        raise StepError("verification failed: " + "; ".join(problems))

    if job.dst.exists() and not ctx.overwrite:
        raise StepError("%s appeared while converting." % job.dst.name)
    try:
        _retry(os.replace, out, job.dst)
    except OSError:
        shutil.copyfile(out, job.dst)
        _remove_file(out)
    job.flac_bytes = job.dst.stat().st_size
    job.state = "done"
    _cleanup_job_files(job, ctx)
    ratio = 100.0 * job.flac_bytes / job.wav_bytes if job.wav_bytes else 0.0
    return "OK  %s, %.1f%% of WAV, verified" % (_human_size(job.flac_bytes), ratio)


def _cleanup_job_files(job: Job, ctx: Ctx) -> None:
    for pattern in ("%04d.*", "%04d_*"):
        for path in ctx.work.glob(pattern % job.index):
            try:
                _remove_file(path)
            except OSError:
                pass


def run_stage(title: str, jobs: List[Job], step: Callable[[Job, Ctx], str], ctx: Ctx,
              workers: int, label: Callable[[Job], str]) -> None:
    say(title)
    total = len(jobs)
    width = len(str(total))
    finished = 0

    def guarded(job: Job) -> str:
        try:
            return step(job, ctx)
        except Cancelled:
            job.state, job.error = "failed", "cancelled"
        except StepError as exc:
            job.state, job.error = "failed", str(exc)
        except Exception as exc:
            job.state, job.error = "failed", "unexpected error: %r" % exc
            if ctx.verbose:
                traceback.print_exc()
        _cleanup_job_files(job, ctx)
        return ""

    with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, workers)) as pool:
        futures = {pool.submit(guarded, job): job for job in jobs}
        pending = set(futures)
        try:
            while pending:
                done, pending = concurrent.futures.wait(
                    pending, timeout=0.25, return_when=concurrent.futures.FIRST_COMPLETED)
                for fut in done:
                    job = futures[fut]
                    finished += 1
                    if job.state == "failed":
                        if job.error != "cancelled":
                            say("  [%*d/%d] %s  FAILED: %s" % (width, finished, total, label(job), job.error))
                    else:
                        say("  [%*d/%d] %s  %s" % (width, finished, total, label(job), fut.result()))
        except KeyboardInterrupt:
            ctx.runner.cancel()
            for fut in pending:
                fut.cancel()
            raise

def _parse_args(argv: Optional[Sequence[str]]) -> argparse.Namespace:
    cpu = os.cpu_count() or 1
    parser = argparse.ArgumentParser(
        description="Losslessly convert ALAC (.m4a/.alac) files to FLAC level 8, keeping all metadata.")
    parser.add_argument("folder", nargs="?", help="folder to convert (default: the folder this script is in)")
    parser.add_argument("-r", "--recursive", action="store_true", help="also convert files in subfolders")
    parser.add_argument("-j", "--jobs", type=int, default=cpu, metavar="N",
                        help="files to encode at the same time (default: %d, the number of CPU threads)" % cpu)
    parser.add_argument("--overwrite", action="store_true", help="replace FLAC files that already exist")
    choice = parser.add_mutually_exclusive_group()
    choice.add_argument("--delete-originals", action="store_true", help="delete the ALAC files without asking")
    choice.add_argument("--keep-originals", action="store_true", help="keep the ALAC files without asking")
    parser.add_argument("--dry-run", action="store_true", help="only show what would be converted, with all tags")
    parser.add_argument("-v", "--verbose", action="store_true", help="show every tag that will be written")
    parser.add_argument("--no-pause", action="store_true", help="never wait for Enter before closing")
    args = parser.parse_args(argv)
    if args.jobs < 1:
        parser.error("--jobs must be at least 1")
    return args


def _pause(args: argparse.Namespace) -> None:
    if args.no_pause:
        return
    try:
        input("Press Enter to close...")
    except (EOFError, KeyboardInterrupt):
        pass


def _fatal(args: argparse.Namespace, message: str) -> int:
    say("")
    say("ERROR: %s" % message)
    _pause(args)
    return 2


def _ask_yes(question: str, no_input_note: str) -> bool:
    while True:
        try:
            answer = input(question).strip().lower()
        except EOFError:
            say(no_input_note)
            return False
        except KeyboardInterrupt:
            say("")
            return False
        if answer in ("", "y", "yes"):
            return True
        if answer in ("n", "no"):
            return False
        say("Please type y or n.")


def _remove_stale_work_dirs(folder: Path) -> None:
    for path in folder.glob(WORK_DIR_PREFIX + "*"):
        try:
            if path.is_dir() and time.time() - path.stat().st_mtime > 6 * 3600:
                say("Removing a leftover temporary folder from an interrupted run: %s" % path.name)
                _remove_tree(path)
        except OSError:
            pass


def main(argv: Optional[Sequence[str]] = None) -> int:
    _setup_console()
    args = _parse_args(argv)
    started = time.monotonic()

    folder = Path(args.folder).expanduser() if args.folder else _script_dir()
    try:
        folder = folder.resolve()
    except OSError:
        pass
    say("=" * 72)
    say(" ALAC -> FLAC")
    say("=" * 72)
    say(" Folder : %s" % folder)
    if not folder.is_dir():
        return _fatal(args, "folder not found: %s" % folder)

    tool_dirs = [_script_dir()]
    if folder != tool_dirs[0]:
        tool_dirs.append(folder)
    ffmpeg = find_tool("ffmpeg", tool_dirs)
    flac = find_tool("flac", tool_dirs)
    missing = [name for name, path in (("ffmpeg", ffmpeg), ("flac", flac)) if path is None]
    if missing:
        names = " and ".join(n + (".exe" if os.name == "nt" else "") for n in missing)
        pronoun = "them" if len(missing) > 1 else "it"
        return _fatal(args, "%s not found. Put %s in the same folder as this script (%s) or add %s to PATH."
                      % (names, pronoun, _script_dir(), pronoun))
    ffmpeg_ver = tool_version(ffmpeg, "-version")
    flac_ver = tool_version(flac, "--version")
    if ffmpeg_ver is None:
        return _fatal(args, "%s was found but does not run" % ffmpeg)
    if flac_ver is None:
        return _fatal(args, "%s was found but does not run (if it came with libFLAC.dll,"
                            " please include it.)" % flac)
    m = re.search(r"(\d+)\.(\d+)(?:\.(\d+))?", flac_ver)
    flac_version = tuple(int(x) for x in m.groups() if x is not None) if m else (0,)
    say(" ffmpeg : %s" % ffmpeg)
    say(" flac   : %s (%s)" % (flac, flac_ver))

    _remove_stale_work_dirs(folder)
    sources = find_sources(folder, args.recursive)
    if not sources and not args.recursive:
        nested = find_sources(folder, True)
        if nested and _ask_yes("No ALAC files in this folder itself, but %d in its subfolders. Convert?"
                               " [Y/N]: " % len(nested), "(no keyboard input available)"):
            args.recursive = True
            sources = nested
    if not sources:
        where = "in %s%s" % (folder, " or its subfolders" if args.recursive else "")
        return _fatal(args, "no .m4a or .alac files found %s" % where)

    jobs: List[Job] = []
    skipped: List[Tuple[str, str]] = []
    targets: Dict[str, str] = {}
    for src in sources:
        rel = str(src.relative_to(folder))
        try:
            job = plan_job(len(jobs) + 1, src, folder, flac_version)
        except StepError as exc:
            skipped.append((rel, str(exc)))
            continue
        key = os.path.normcase(str(job.dst))
        if key in targets:
            skipped.append((rel, "would also become %s (already used by %s)" % (job.dst.name, targets[key])))
            continue
        if job.dst.exists() and not args.overwrite:
            skipped.append((rel, "%s already exists (use --overwrite to replace it)" % job.dst.name))
            continue
        targets[key] = rel
        jobs.append(job)

    say(" Found  : %d ALAC file(s) to convert%s" % (len(jobs), (", %d skipped" % len(skipped)) if skipped else ""))
    for rel, reason in skipped:
        say("   skipped %s: %s" % (rel, reason))
    if args.dry_run or args.verbose:
        say("")
        for job in jobs:
            describe_job(job)
    if args.dry_run:
        say("")
        say("Dry run: nothing was converted.")
        return 0
    if not jobs:
        say("")
        say("Nothing to convert.")
        _pause(args)
        return 0

    work = folder / ("%s%d" % (WORK_DIR_PREFIX, os.getpid()))
    try:
        work.mkdir()
    except OSError as exc:
        return _fatal(args, "cannot create a temporary folder in %s (%s)" % (folder, exc.strerror))
    ctx = Ctx(ffmpeg=ffmpeg, flac=flac, work=work, runner=Runner(),
              overwrite=args.overwrite, verbose=args.verbose)
    interrupted = False
    try:
        try:
            batches = plan_batches(jobs, shutil.disk_usage(str(work)).free)
        except StepError as exc:
            return _fatal(args, str(exc))
        if len(batches) > 1:
            say(" Note: Not enough disk space for every temporary file."
                " Working in %d batches." % len(batches))
        decode_workers = min(args.jobs, 4)
        for n, batch in enumerate(batches, 1):
            prefix = ("Batch %d/%d - " % (n, len(batches))) if len(batches) > 1 else ""
            say("")
            run_stage("%sStep 1/2: Decoding ALAC -> WAV" % prefix, batch, decode_to_wav, ctx,
                      decode_workers, lambda j: j.rel)
            decoded = [j for j in batch if j.state == "decoded"]
            if not decoded:
                continue
            say("")
            run_stage("%sStep 2/2: Encoding WAV -> FLAC %s" % (prefix, FLAC_LEVEL), decoded,
                      encode_to_flac, ctx, args.jobs, lambda j: str(Path(j.rel).with_suffix(".flac")))
    except KeyboardInterrupt:
        interrupted = True
        ctx.runner.cancel()
    finally:
        if not _remove_tree(work):
            say("Could not remove the temporary folder %s." % work)

    done = [j for j in jobs if j.state == "done"]
    failed = [j for j in jobs if j.state != "done"]
    if interrupted:
        say("")
        say("Stopped (Ctrl+C). %d file(s) were finished. No originals deleted." % len(done))
        return 130

    say("")
    say("=" * 72)
    say(" Converted : %d" % len(done))
    if failed:
        say(" Failed    : %d" % len(failed))
        for job in failed:
            say("   %s: %s" % (job.rel, job.error or "not converted"))
    if skipped:
        say(" Skipped   : %d" % len(skipped))
    flagged = [j for j in done if j.blocking]
    for job in flagged:
        for problem in job.blocking:
            say(" Warning   : %s: %s" % (job.rel, problem))
    if args.verbose:
        for job in done:
            for note in job.notes:
                say(" Note      : %s: %s" % (job.rel, note))
    if done:
        wav_total = sum(j.wav_bytes for j in done)
        flac_total = sum(j.flac_bytes for j in done)
        src_total = sum(j.src.stat().st_size for j in done if j.src.exists())
        say(" Size      : ALAC %s -> FLAC %s (%.1f%% of uncompressed)"
            % (_human_size(src_total), _human_size(flac_total), 100.0 * flac_total / max(1, wav_total)))
    say(" Time      : %s" % _human_duration(time.monotonic() - started))
    say("=" * 72)

    deletable = [j for j in done if not j.blocking]
    if flagged:
        say("%d converted file(s) had warnings, so their originals will be kept." % len(flagged))
    if deletable:
        if args.delete_originals:
            delete = True
        elif args.keep_originals:
            delete = False
        else:
            delete = _ask_yes("Delete the %d original ALAC file(s)? [Y/N]: " % len(deletable),
                              "(No keyboard input available. Keeping the originals.)")
        if delete:
            removed = 0
            for job in deletable:
                try:
                    _remove_file(job.src)
                    removed += 1
                except OSError as exc:
                    say("  could not delete %s (%s)" % (job.rel, exc.strerror))
            say("Deleted %d original file(s)." % removed)
        else:
            say("Kept the original files.")
    elif not done:
        _pause(args)
    return 0 if not failed else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        sys.exit(130)