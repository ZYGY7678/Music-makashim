// SongOrganizer - Windows GUI version
// Build validation 2026-10-04
// Scans a folder (e.g. an SD card drive letter) for audio files, copies/moves
// them into a root "כל השירים" folder. It indexes filenames and embedded music
// metadata, detects repeated names/phrases, asks the user which unknown repeats
// deserve folders, automatically accepts known artists, and alphabetizes the rest.

#define _CRT_SECURE_NO_WARNINGS
#define UNICODE
#define _UNICODE
#define WINVER 0x0601
#define _WIN32_WINNT 0x0601

#include <windows.h>
#include <commctrl.h>
#include <shlobj.h>
#include <shobjidl.h>
#include <propsys.h>
#include <propkey.h>
#include <winhttp.h>
#include <stdio.h>
#include <stdlib.h>
#include <wchar.h>
#include <wctype.h>
#include <string.h>
#include <ctype.h>
#include <stdarg.h>

#pragma comment(lib, "comctl32.lib")
#pragma comment(lib, "shell32.lib")
#pragma comment(lib, "ole32.lib")
#pragma comment(lib, "propsys.lib")
#pragma comment(lib, "winhttp.lib")

/* ============================= data / logic ============================= */
/*
 * "The engine" - rebuilt from scratch. Self-contained: it never touches GUI
 * state directly, only reports through logLineW()/setProgress() (implemented
 * below in the GUI layer, forward-declared here), so it can keep running
 * safely on a background thread.
 *
 * Two real bugs in the previous version explain why it looked broken:
 *
 *   1. Every copy called CopyFileW(..., TRUE) - "fail if the destination
 *      already exists". The very first pass, which flattens every audio file
 *      into "כל השירים", therefore failed outright the moment two source
 *      files anywhere on the card shared a filename - extremely common with
 *      generic names like "01.mp3", "Recording.amr", "audio.m4a" that show
 *      up in more than one folder. The same flag also meant that simply
 *      running the tool a second time on an already-organized folder failed
 *      on every single file, since the destination now already existed.
 *   2. Word lookup while building the shared-word index did a linear scan
 *      over every unique word seen so far, for every word of every song
 *      (findOrAddWord). That's fine for a couple hundred songs, but on a
 *      real phone with several thousand tracks it's effectively an O(n^2)
 *      scan and can take a very long time to finish - which looks exactly
 *      like "the app hangs" even though it would eventually complete.
 *
 * Fixes: a real hash table for word lookup, and collision-safe destination
 * naming that never overwrites a different file and never just fails on a
 * name clash (resolveDestPath / copyOrMove / copyIntoGroup below).
 */

#define MAX_SONGS 20000
#define MIN_WORD_LENGTH 3
#define MAX_WORDS_PER_SONG 24
#define MAX_UNIQUE_PAIRS 40000
#define PAIR_HASH_SIZE 65536   /* power of two, > MAX_UNIQUE_PAIRS so buckets stay short */
#define MAX_EXCLUDE_DIRS 64

static const wchar_t *AUDIO_EXT[] = {
    // common
    L".mp3", L".wav", L".flac", L".ogg", L".oga", L".m4a", L".m4b", L".m4p", L".m4r",
    L".aac", L".wma", L".opus", L".mid", L".midi", L".amr", L".awb",
    // less common but still found on phones / older devices
    L".ape", L".aiff", L".aif", L".aifc", L".alac", L".dsf", L".dff", L".wv", L".tta",
    L".ac3", L".mka", L".caf", L".3gp", L".3ga", L".spx", L".ra", L".rm", L".voc",
    L".gsm", L".au", L".snd", L".mpc", L".weba", L".mp2", L".mp1", L".mogg", L".adts",
    NULL
};

static const wchar_t *STOP_WORDS[] = {
    L"אני", L"אתה", L"את", L"אתם", L"אתן", L"הוא", L"היא", L"הם", L"הן", L"אנחנו",
    L"של", L"עם", L"אם", L"לא", L"כן", L"זה", L"זאת", L"אלה", L"אלו", L"גם", L"רק",
    L"כי", L"על", L"אל", L"יש", L"אין", L"מה", L"מי", L"כל", L"עוד", L"אבל", L"או",
    L"כמו", L"היה", L"היו", L"הייתי", L"להיות", L"כאשר", L"כדי", L"בין", L"אחד",
    L"אחת", L"שני", L"שתי", L"לי", L"לך", L"לו", L"לה", L"לנו", L"לכם",
    L"the", L"and", L"for", L"with", L"you", L"your", L"are", L"was", L"this", L"that",
    NULL
};

/* ===================== רשימת זמרים ידועה (למיון לפי זמר) =====================
 * רשימה מובנית של שמות זמרים. משמשת את מצב "מיון לפי רשימת זמרים": שיר
 * ששמו (הכותרת) מכיל את רצף המילים של אחד השמות האלה משויך לאותו זמר. */
#include "artist_array.c"

typedef struct {
    wchar_t path[MAX_PATH];
    wchar_t fileName[MAX_PATH];
    wchar_t title[MAX_PATH];
    wchar_t originDir[MAX_PATH]; // leaf name of the folder this file was found in
    wchar_t metaTitle[MAX_PATH];
    wchar_t artist[MAX_PATH];
    wchar_t album[MAX_PATH];
    wchar_t albumArtist[MAX_PATH];
    wchar_t composer[MAX_PATH];
    wchar_t conductor[MAX_PATH];
    wchar_t contentGroup[MAX_PATH];
    wchar_t publisher[MAX_PATH];
    wchar_t subtitle[MAX_PATH];
    wchar_t writer[MAX_PATH];
    wchar_t producer[MAX_PATH];
} Song;

typedef struct {
    int songIndex;
    int next;
} PairNode;

/* A "pair" is two content words that appear back-to-back (no word, not even a
 * stop word, between them) in a title, in that order - e.g. "אהבה גדולה". */
typedef struct {
    wchar_t key[130];      // normalized "word1 word2", used for hashing/lookup
    wchar_t display[130];  // original-casing "Word1 Word2", used as folder name
    int headNode;   // linked list (through nodePool) of songs containing this pair
    int count;
    int hashNext;   // next pair entry that hashed into the same bucket
} PairEntry;

static Song *songs;
static int songCount = 0;

static PairEntry *pairs;
static int pairCount = 0;
static int pairHashTable[PAIR_HASH_SIZE];

/* For each song, the list of pair-indices (into `pairs`) formed from its
 * title, in order - needed after indexing to pick, per song, whichever of
 * its pairs is shared with the most other songs. */
static int (*songPairIndex)[MAX_WORDS_PER_SONG];
static int songPairCount_[MAX_SONGS];

static PairNode *nodePool;
static int nodePoolCount = 0;

/* Per-song folder assignment resolved after indexing: the pair index the
 * song will actually be copied under, or -1 if it shares no pair (count>=2)
 * with any other song and therefore falls into miscDirName. */
static int *assignedPair;

static wchar_t rootDir[MAX_PATH];
static const wchar_t miscDirName[] = L"שירים שונים";
static const wchar_t rootDirName[] = L"כל השירים";
static const wchar_t artistsRootDirName[] = L"כל הזמרים";
static const wchar_t notIdentifiedDirName[] = L"לא מזוהים";

/* Folders the user chose to exclude entirely from the scan - never counted,
 * never recursed into, never copied. Compared by full absolute path. */
static wchar_t excludeDirs[MAX_EXCLUDE_DIRS][MAX_PATH];
static int excludeDirCount = 0;

static int copiedCount = 0;
static int skippedDuplicateCount = 0;
static int skippedByUserCount = 0;
static int errorCount = 0;

/* Set from the UI thread (skip button) and polled from the copy-progress
 * callback below, so a single stuck file (common on flaky SD cards / MTP
 * phone storage) can be aborted without killing the whole run. Cleared
 * before every new file so the flag never "carries over" to the next one. */
static volatile LONG g_skipRequested = 0;

/* diagnostics to help tell "found nothing at all" apart from "found files,
   but none matched a known audio extension" */
static int totalFilesSeen = 0;
static int accessDeniedDirs = 0;
static wchar_t sampleExtensions[12][16];
static int sampleExtCount = 0;

static void noteExtension(const wchar_t *fileName) {
    const wchar_t *dot = wcsrchr(fileName, L'.');
    if (!dot || sampleExtCount >= 12) return;
    for (int i = 0; i < sampleExtCount; i++)
        if (_wcsicmp(sampleExtensions[i], dot) == 0) return;
    wcsncpy(sampleExtensions[sampleExtCount], dot, 15);
    sampleExtensions[sampleExtCount][15] = 0;
    sampleExtCount++;
}

/* forward decl for logging from worker thread into the UI */
static void logLineW(const wchar_t *fmt, ...);
static void setProgress(int value, int max);
static void setProgressFolders(int value, int max);
static void setProgressOverall(int value, int max);
static void setCurrentFile(const wchar_t *title);

/* GUI handles/events the engine needs to reach across to the UI thread for
 * the candidate-pair review step - real definitions are further down with
 * the rest of the GUI globals; forward-declared here so the engine (above
 * the GUI section) can use them. */
static HWND g_hMain;
static HANDLE g_reviewDoneEvent;
#define WM_APP_SHOW_REVIEW (WM_APP + 7)

typedef struct { wchar_t name[130]; int pairIndex; int songCount; int approved; } CandidatePair;
static CandidatePair candidatePairs[MAX_UNIQUE_PAIRS];
static int candidatePairCount = 0;

/* Set right before PostMessage(WM_APP_SHOW_REVIEW) to tell the (shared)
 * review window which of the two callers is showing it: the "candidate
 * pairs" flow (unsure matches, unchecked by default) or the "artist list"
 * flow (every row is an already-certain match from ARTIST_LIST, checked by
 * default - the user unchecks whichever don't belong before continuing). */
static int g_reviewIsArtistMode = 0;

static int isStopWord(const wchar_t *w) {
    for (int i = 0; STOP_WORDS[i]; i++) {
        if (_wcsicmp(w, STOP_WORDS[i]) == 0) return 1;
    }
    return 0;
}

static int hasAudioExt(const wchar_t *fileName) {
    const wchar_t *dot = wcsrchr(fileName, L'.');
    if (!dot) return 0;
    for (int i = 0; AUDIO_EXT[i]; i++) {
        if (_wcsicmp(dot, AUDIO_EXT[i]) == 0) return 1;
    }
    return 0;
}

static void stripExtension(const wchar_t *fileName, wchar_t *out, size_t outSize) {
    wcsncpy(out, fileName, outSize - 1);
    out[outSize - 1] = 0;
    wchar_t *dot = wcsrchr(out, L'.');
    if (dot) *dot = 0;
}

/* Locale-independent Unicode letter/digit test and lowercasing, using the Win32
   API rather than the CRT's iswalnum/towlower - the CRT versions are tied to the
   process locale and are not reliable for classifying Hebrew letters as
   alphanumeric, which would silently break all word-based grouping. */
static int isWordChar(wchar_t c) {
    return IsCharAlphaNumericW(c) != 0;
}

static wchar_t toLowerChar(wchar_t c) {
    wchar_t buf[2] = { c, 0 };
    CharLowerW(buf);
    return buf[0];
}

static void toLowerCopy(const wchar_t *in, wchar_t *out, size_t outSize) {
    size_t i = 0;
    for (; in[i] && i < outSize - 1; i++) out[i] = toLowerChar(in[i]);
    out[i] = 0;
}

static wchar_t *sanitizeFileNameInPlace(wchar_t *name) {
    for (wchar_t *p = name; *p; p++) {
        if (wcschr(L"\\/:*?\"<>|", *p)) *p = L'_';
    }
    return name;
}

/* True if `dir` is (exactly) one of the user's excluded folders. Checked at
 * the point scanDir is about to recurse into it, so nothing beneath an
 * excluded folder is ever seen, counted, or copied. */
static int isPathExcluded(const wchar_t *dir) {
    for (int i = 0; i < excludeDirCount; i++) {
        if (_wcsicmp(excludeDirs[i], dir) == 0) return 1;
    }
    return 0;
}

/* Read textual music metadata through the Windows Shell property system. */
static void propVariantToText(const PROPVARIANT *pv, wchar_t *out, size_t outCap) {
    if (!out || outCap == 0) return;
    out[0] = 0;
    if (!pv) return;
    if (pv->vt == VT_LPWSTR && pv->pwszVal) {
        wcsncpy(out, pv->pwszVal, outCap - 1);
        out[outCap - 1] = 0;
    } else if (pv->vt == VT_BSTR && pv->bstrVal) {
        wcsncpy(out, pv->bstrVal, outCap - 1);
        out[outCap - 1] = 0;
    } else if ((pv->vt & VT_VECTOR) && (pv->vt & VT_LPWSTR) && pv->calpwstr.cElems && pv->calpwstr.pElems) {
        size_t used = 0;
        for (ULONG i = 0; i < pv->calpwstr.cElems && used < outCap - 1; i++) {
            const wchar_t *v = pv->calpwstr.pElems[i];
            if (!v || !v[0]) continue;
            if (used) {
                if (used + 2 >= outCap) break;
                out[used++] = L';';
                out[used++] = L' ';
            }
            size_t room = outCap - used - 1;
            size_t n = wcslen(v);
            if (n > room) n = room;
            wmemcpy(out + used, v, n);
            used += n;
            out[used] = 0;
        }
    } else if (pv->vt == VT_LPSTR && pv->pszVal) {
        MultiByteToWideChar(CP_ACP, 0, pv->pszVal, -1, out, (int)outCap);
        out[outCap - 1] = 0;
    }
}

static void readStringProperty(IPropertyStore *store, REFPROPERTYKEY key, wchar_t *out, size_t outCap) {
    out[0] = 0;
    if (!store) return;
    PROPVARIANT pv;
    PropVariantInit(&pv);
    if (SUCCEEDED(store->lpVtbl->GetValue(store, key, &pv)))
        propVariantToText(&pv, out, outCap);
    PropVariantClear(&pv);
}

static void readMusicMetadata(const wchar_t *path, Song *s) {
    s->metaTitle[0] = s->artist[0] = s->album[0] = s->albumArtist[0] = s->composer[0] = 0;
    s->conductor[0] = s->contentGroup[0] = s->publisher[0] = s->subtitle[0] = 0;
    s->writer[0] = s->producer[0] = 0;
    IPropertyStore *store = NULL;
    HRESULT hr = SHGetPropertyStoreFromParsingName(path, NULL, GPS_BESTEFFORT, &IID_IPropertyStore, (void **)&store);
    if (SUCCEEDED(hr) && store) {
        readStringProperty(store, &PKEY_Title, s->metaTitle, MAX_PATH);
        readStringProperty(store, &PKEY_Music_Artist, s->artist, MAX_PATH);
        readStringProperty(store, &PKEY_Music_AlbumTitle, s->album, MAX_PATH);
        readStringProperty(store, &PKEY_Music_AlbumArtist, s->albumArtist, MAX_PATH);
        readStringProperty(store, &PKEY_Music_Composer, s->composer, MAX_PATH);
        readStringProperty(store, &PKEY_Music_Conductor, s->conductor, MAX_PATH);
        readStringProperty(store, &PKEY_Music_ContentGroupDescription, s->contentGroup, MAX_PATH);
        readStringProperty(store, &PKEY_Media_Publisher, s->publisher, MAX_PATH);
        readStringProperty(store, &PKEY_Media_SubTitle, s->subtitle, MAX_PATH);
        readStringProperty(store, &PKEY_Media_Writer, s->writer, MAX_PATH);
        readStringProperty(store, &PKEY_Media_Producer, s->producer, MAX_PATH);
        store->lpVtbl->Release(store);
    }
}

static void scanDir(const wchar_t *dir) {
    wchar_t pattern[MAX_PATH];
    swprintf(pattern, MAX_PATH, L"%ls\\*", dir);

    WIN32_FIND_DATAW fd;
    HANDLE h = FindFirstFileW(pattern, &fd);
    if (h == INVALID_HANDLE_VALUE) {
        DWORD err = GetLastError();
        if (err != ERROR_FILE_NOT_FOUND) { // empty folder is fine, not an error
            accessDeniedDirs++;
            if (accessDeniedDirs <= 5) // cap the spam for phones with many protected folders
                logLineW(L"  לא ניתן לגשת לתיקייה: %ls (קוד שגיאה %d)", dir, (int)err);
        }
        return;
    }

    do {
        if (wcscmp(fd.cFileName, L".") == 0 || wcscmp(fd.cFileName, L"..") == 0) continue;

        wchar_t fullPath[MAX_PATH];
        swprintf(fullPath, MAX_PATH, L"%ls\\%ls", dir, fd.cFileName);

        if (fd.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) {
            if (wcscmp(fd.cFileName, rootDirName) != 0 && !isPathExcluded(fullPath))
                scanDir(fullPath);
        } else {
            totalFilesSeen++;
            noteExtension(fd.cFileName);
            if (hasAudioExt(fd.cFileName) && songCount < MAX_SONGS) {
                Song *s = &songs[songCount];
                wcsncpy(s->path, fullPath, MAX_PATH - 1);
                wcsncpy(s->fileName, fd.cFileName, MAX_PATH - 1);
                stripExtension(fd.cFileName, s->title, MAX_PATH);
                // leaf name of the folder this file sat in, e.g. "...\Downloads\Old Phone" -> "Old Phone"
                const wchar_t *slash = wcsrchr(dir, L'\\');
                wcsncpy(s->originDir, slash ? slash + 1 : dir, MAX_PATH - 1);
                s->originDir[MAX_PATH - 1] = 0;
                readMusicMetadata(fullPath, s);
                songCount++;
            }
        }
    } while (FindNextFileW(h, &fd));

    FindClose(h);
}

/* FNV-1a over the normalized (already-lowercased) pair key. */
static unsigned int hashKey(const wchar_t *w) {
    unsigned int h = 2166136261u;
    for (; *w; w++) {
        h ^= (unsigned int)(unsigned short)*w;
        h *= 16777619u;
    }
    return h;
}

/* O(1)-average lookup via a real hash table instead of a linear scan over
   every pair seen so far - a linear scan here would make indexing a large
   library (thousands of songs) effectively O(n^2) and could take a very
   long time, which looked exactly like a hung/broken engine. */
static int findOrAddPair(const wchar_t *normalized, const wchar_t *display) {
    unsigned int bucket = hashKey(normalized) & (PAIR_HASH_SIZE - 1);
    for (int i = pairHashTable[bucket]; i != -1; i = pairs[i].hashNext) {
        if (wcscmp(pairs[i].key, normalized) == 0) return i;
    }
    if (pairCount >= MAX_UNIQUE_PAIRS) return -1;

    int idx = pairCount++;
    wcsncpy(pairs[idx].key, normalized, 129);
    pairs[idx].key[129] = 0;
    wcsncpy(pairs[idx].display, display, 129);
    pairs[idx].display[129] = 0;
    pairs[idx].count = 0;
    pairs[idx].headNode = -1;
    pairs[idx].hashNext = pairHashTable[bucket];
    pairHashTable[bucket] = idx;
    return idx;
}

static void addSongToPair(int pi, int songIndex) {
    if (pi < 0 || nodePoolCount >= MAX_SONGS * MAX_WORDS_PER_SONG) return;
    for (int k = 0; k < songPairCount_[songIndex]; k++)
        if (songPairIndex[songIndex][k] == pi) return;
    int node = nodePoolCount++;
    nodePool[node].songIndex = songIndex;
    nodePool[node].next = pairs[pi].headNode;
    pairs[pi].headNode = node;
    pairs[pi].count++;

    if (songPairCount_[songIndex] < MAX_WORDS_PER_SONG)
        songPairIndex[songIndex][songPairCount_[songIndex]++] = pi;
}

/* Index a complete text value and its consecutive meaningful two-word phrases.
   Exact full-value duplicates catch repeated artist/album/title metadata even
   when the value is only one word. Two-word phrases catch repeated names inside
   longer titles. */
static void addDuplicateTextForSong(int songIndex, const wchar_t *text) {
    if (!text || !text[0]) return;

    wchar_t normFull[MAX_PATH];
    toLowerCopy(text, normFull, MAX_PATH);
    int fullPi = findOrAddPair(normFull, text);
    addSongToPair(fullPi, songIndex);

    wchar_t buf[MAX_PATH];
    wcsncpy(buf, text, MAX_PATH - 1);
    buf[MAX_PATH - 1] = 0;
    wchar_t contentOrig[MAX_WORDS_PER_SONG][64];
    wchar_t contentNorm[MAX_WORDS_PER_SONG][64];
    int contentCount = 0;

    wchar_t *p = buf;
    while (*p && contentCount < MAX_WORDS_PER_SONG) {
        while (*p && !isWordChar(*p)) p++;
        if (!*p) break;
        wchar_t *startWord = p;
        while (*p && isWordChar(*p)) p++;
        size_t len = (size_t)(p - startWord);
        if (len >= MIN_WORD_LENGTH && len < 64) {
            wchar_t original[64];
            wcsncpy(original, startWord, len);
            original[len] = 0;
            wchar_t normalized[64];
            toLowerCopy(original, normalized, 64);
            if (!isStopWord(normalized)) {
                wcsncpy(contentOrig[contentCount], original, 63);
                contentOrig[contentCount][63] = 0;
                wcsncpy(contentNorm[contentCount], normalized, 63);
                contentNorm[contentCount][63] = 0;
                contentCount++;
            }
        }
    }

    for (int k = 0; k + 1 < contentCount; k++) {
        wchar_t displayPair[130];
        swprintf(displayPair, 130, L"%ls %ls", contentOrig[k], contentOrig[k + 1]);
        wchar_t normalizedPair[130];
        swprintf(normalizedPair, 130, L"%ls %ls", contentNorm[k], contentNorm[k + 1]);
        int pi = findOrAddPair(normalizedPair, displayPair);
        addSongToPair(pi, songIndex);
    }
}

/* Scan all textual song-name fields we can read from Windows. Genre is not
   included because a common genre is not a useful duplicate folder name. */
static void buildPairIndex(void) {
    for (int i = 0; i < songCount; i++) {
        addDuplicateTextForSong(i, songs[i].title);        /* filename title */
        addDuplicateTextForSong(i, songs[i].metaTitle);   /* embedded title */
        addDuplicateTextForSong(i, songs[i].artist);      /* artist */
        addDuplicateTextForSong(i, songs[i].album);       /* album */
        addDuplicateTextForSong(i, songs[i].albumArtist); /* album artist */
        addDuplicateTextForSong(i, songs[i].composer);    /* composer */
        addDuplicateTextForSong(i, songs[i].conductor);    /* conductor */
        addDuplicateTextForSong(i, songs[i].contentGroup); /* content group */
        addDuplicateTextForSong(i, songs[i].publisher);    /* publisher */
        addDuplicateTextForSong(i, songs[i].subtitle);     /* subtitle */
        addDuplicateTextForSong(i, songs[i].writer);       /* writer */
        addDuplicateTextForSong(i, songs[i].producer);     /* producer */
    }
}

/* For every song, picks whichever of its pairs is shared with the most other
 * songs (count >= 2) as the folder it will be copied into; songs with no
 * such pair are left at -1 (they land in miscDirName). */
static void buildGroupAssignment(void) {
    for (int i = 0; i < songCount; i++) {
        int best = -1, bestCount = 0;
        for (int k = 0; k < songPairCount_[i]; k++) {
            int pi = songPairIndex[i][k];
            if (pairs[pi].count >= 2 && pairs[pi].count > bestCount) {
                bestCount = pairs[pi].count;
                best = pi;
            }
        }
        assignedPair[i] = best;
    }
}

static int samePath(const wchar_t *a, const wchar_t *b) {
    return _wcsicmp(a, b) == 0;
}

/* Heuristic "is this already the same song" check, used to make reruns on an
   already-organized folder safe: if a file already sitting at the
   destination has the same size as the source, treat it as the same track
   already organized there and skip re-copying it - instead of either
   failing (the old bFailIfExists=TRUE behaviour) or silently overwriting a
   possibly-different file that just happens to share a name. Not a perfect
   content check, but a deliberate, cheap tradeoff that never destroys data. */
static int sameSizeFile(const wchar_t *a, const wchar_t *b) {
    WIN32_FILE_ATTRIBUTE_DATA da, db;
    if (!GetFileAttributesExW(a, GetFileExInfoStandard, &da)) return 0;
    if (!GetFileAttributesExW(b, GetFileExInfoStandard, &db)) return 0;
    return da.nFileSizeHigh == db.nFileSizeHigh && da.nFileSizeLow == db.nFileSizeLow;
}

/* Picks a destination path under destDir for fileName that is safe to write to:
   - the plain name, if nothing is there yet;
   - the plain name, if what's there is already this exact source file;
   - the plain name, if what's there looks like the same song already
     organized here (same size) - *alreadyThere is set and the caller skips
     copying instead of treating it as an error;
   - otherwise "name (2).ext", "name (3).ext", ... - so a genuinely different
     file that happens to share a name (very common on phones: "01.mp3",
     "Recording.amr", "audio.m4a" turning up in several folders) is never
     silently overwritten and never simply fails to copy. */
static int resolveDestPath(const wchar_t *destDir, const wchar_t *fileName,
                            const wchar_t *srcPath, wchar_t *out, size_t outSize,
                            int *alreadyThere) {
    *alreadyThere = 0;
    swprintf(out, outSize, L"%ls\\%ls", destDir, fileName);

    if (GetFileAttributesW(out) == INVALID_FILE_ATTRIBUTES) return 1;
    if (samePath(srcPath, out)) return 1;
    if (sameSizeFile(srcPath, out)) { *alreadyThere = 1; return 1; }

    wchar_t base[MAX_PATH], ext[32];
    wcsncpy(base, fileName, MAX_PATH - 1);
    base[MAX_PATH - 1] = 0;
    wchar_t *dot = wcsrchr(base, L'.');
    if (dot) { wcsncpy(ext, dot, 31); ext[31] = 0; *dot = 0; }
    else ext[0] = 0;

    for (int n = 2; n < 1000; n++) {
        swprintf(out, outSize, L"%ls\\%ls (%d)%ls", destDir, base, n, ext);
        if (GetFileAttributesW(out) == INVALID_FILE_ATTRIBUTES) return 1;
        if (samePath(srcPath, out)) return 1;
        if (sameSizeFile(srcPath, out)) { *alreadyThere = 1; return 1; }
    }
    return 0; // pathological: 998 same-named, different-sized files - give up
}

/* Progress callback shared by CopyFileExW / MoveFileWithProgressW: called
 * periodically by Windows while a single file is in flight. Polling
 * g_skipRequested here - rather than only before/after the call - is what
 * lets "skip" actually interrupt a file that's stuck mid-transfer instead
 * of only taking effect on the *next* file. */
static DWORD CALLBACK copyProgressCallback(
    LARGE_INTEGER TotalFileSize, LARGE_INTEGER TotalBytesTransferred,
    LARGE_INTEGER StreamSize, LARGE_INTEGER StreamBytesTransferred,
    DWORD dwStreamNumber, DWORD dwCallbackReason,
    HANDLE hSourceFile, HANDLE hDestinationFile, LPVOID lpData) {
    (void)TotalFileSize; (void)TotalBytesTransferred; (void)StreamSize; (void)StreamBytesTransferred;
    (void)dwStreamNumber; (void)dwCallbackReason; (void)hSourceFile; (void)hDestinationFile; (void)lpData;
    return g_skipRequested ? PROGRESS_CANCEL : PROGRESS_CONTINUE;
}

/* Returns 1 = copied, 0 = real failure, -1 = aborted via the skip button. */
static int copyFileSkippable(const wchar_t *src, const wchar_t *dest) {
    if (CopyFileExW(src, dest, copyProgressCallback, NULL, NULL, 0)) return 1;
    if (g_skipRequested) { DeleteFileW(dest); return -1; }
    return 0;
}

/* Returns 1 = moved, 0 = real failure, -1 = aborted via the skip button. */
static int moveFileSkippable(const wchar_t *src, const wchar_t *dest) {
    if (MoveFileWithProgressW(src, dest, copyProgressCallback, NULL, MOVEFILE_COPY_ALLOWED)) return 1;
    if (g_skipRequested) { DeleteFileW(dest); return -1; }
    return 0;
}

/* Returns 1 = success, 0 = real failure, -1 = user hit "skip" on this file. */
static int copyOrMove(const wchar_t *src, const wchar_t *destDir, const wchar_t *fileName,
                       int moveMode, wchar_t *outPath, size_t outSize) {
    int already = 0;
    if (!resolveDestPath(destDir, fileName, src, outPath, outSize, &already)) return 0;
    if (already) { skippedDuplicateCount++; return 1; }
    if (samePath(src, outPath)) return 1;

    InterlockedExchange(&g_skipRequested, 0);
    if (moveMode) {
        int r = moveFileSkippable(src, outPath);
        if (r != 0) return r;
        r = copyFileSkippable(src, outPath);
        if (r == 1) { DeleteFileW(src); return 1; } // copied ok even if the source delete fails
        return r;
    }
    return copyFileSkippable(src, outPath);
}

/* Returns 1 = success, 0 = real failure, -1 = user hit "skip" on this file. */
static int copyIntoGroup(const Song *s, const wchar_t *destDir) {
    wchar_t dest[MAX_PATH];
    int already = 0;
    if (!resolveDestPath(destDir, s->fileName, s->path, dest, MAX_PATH, &already)) return 0;
    if (already) return 1;
    if (samePath(s->path, dest)) return 1;
    InterlockedExchange(&g_skipRequested, 0);
    return copyFileSkippable(s->path, dest);
}

/* ===================== מצב מיון לפי רשימת זמרים ===================== */

static const wchar_t artistRootDirName[]      = L"מיון לפי זמרים";
static const wchar_t identifiedRootDirName[]  = L"זמרים מזוהים";
static const wchar_t unidentifiedDirName[]    = L"לא מזוהים";
static const wchar_t offlineAlphabetRootName[] = L"מסודר לפי א ב";
static const wchar_t offlineOtherDirName[] = L"אחר";

/* For A-B sorting: find the first Hebrew letter anywhere in the filename after
   any leading spaces/digits/symbols. Example: "1 ים גדול" -> י. If no Hebrew
   letter exists, use the first non-space character itself as the folder name. */
static wchar_t offlineAlphabetFolderChar(const wchar_t *fileName) {
    if (!fileName) return 0;
    const wchar_t *p = fileName;
    while (*p && iswspace(*p)) p++;
    const wchar_t *first = p;
    static const wchar_t hebrewLetters[] = L"אבגדהוזחטיכלמנסעפצקרשת";
    for (; *p; p++) {
        for (int i = 0; hebrewLetters[i] != 0; i++)
            if (*p == hebrewLetters[i]) return *p;
    }
    return first && *first ? *first : 0;
}

static int createOfflineAlphabetTree(const wchar_t *parentRoot, wchar_t *outRoot, size_t outSize) {
    swprintf(outRoot, outSize, L"%ls\\%ls", parentRoot, offlineAlphabetRootName);
    if (!CreateDirectoryW(outRoot, NULL) && GetLastError() != ERROR_ALREADY_EXISTS) return 0;
    return 1;
}

static void offlineAlphabetDestination(const wchar_t *alphabetRoot, const wchar_t *fileName, wchar_t *outDir, size_t outSize) {
    wchar_t c = offlineAlphabetFolderChar(fileName);
    if (!c) c = L'_';
    if (wcschr(L"\\/:*?\"<>|", c)) c = L'_';
    swprintf(outDir, outSize, L"%ls\\%lc", alphabetRoot, c);
}

#define MAX_ARTIST_WORDS 6
#define MAX_TITLE_WORDS  40

static wchar_t artistWords[ARTIST_COUNT][MAX_ARTIST_WORDS][64];
static int artistWordCount[ARTIST_COUNT];
static int artistTokensBuilt = 0;

/* Splits text into normalized (lower-cased) word tokens using the same
 * word-character rule as the rest of the engine (isWordChar), so an artist
 * name and a song title are tokenized identically and can be compared
 * word-by-word regardless of punctuation, quotes, or hyphens between them. */
static int tokenizeWords(const wchar_t *text, wchar_t out[][64], int maxWords) {
    int n = 0;
    const wchar_t *p = text;
    while (*p && n < maxWords) {
        while (*p && !isWordChar(*p)) p++;
        if (!*p) break;
        const wchar_t *start = p;
        while (*p && isWordChar(*p)) p++;
        size_t len = p - start;
        if (len > 0 && len < 64) {
            wchar_t original[64];
            wcsncpy(original, start, len);
            original[len] = 0;
            toLowerCopy(original, out[n], 64);
            n++;
        }
    }
    return n;
}

static void buildArtistTokens(void) {
    if (artistTokensBuilt) return;
    for (int a = 0; a < ARTIST_COUNT; a++) {
        artistWordCount[a] = tokenizeWords(ARTIST_LIST[a], artistWords[a], MAX_ARTIST_WORDS);
    }
    artistTokensBuilt = 1;
}

/* ===================== התאמה מקורבת (סובלנית לשגיאות כתיב) =====================
 * שם זמר עלול להופיע בכותרת בכתיב מעט שונה מהרשימה המובנית - למשל אות
 * שנדבקה בטעות למילה הבאה ("ועומר אדם"), מילה שנשמטה ("חנן ארי" במקום
 * "חנן בן ארי"), או פשוט טעות הקלדה בתוך מילה ("אלייצור" במקום שם דומה).
 * כדי לזהות זמר גם במקרים כאלה, ההתאמה מתבצעת ברמת המילים (לא התאמת
 * wcscmp מדויקת בלבד) ומתירה "שגיאה" אחת (טעות-אות בתוך מילה) לכל מילה
 * בשם, פרט למילה הראשונה - כלומר שם ארוך יותר מקבל תקציב שגיאות גדול
 * יותר. כל אחד מהבאים נחשב לשגיאה אחת:
 *   - מילה בכותרת שהיא "כמעט" מילה מהשם (שונה ב-MAX_WORD_TYPO_DISTANCE
 *     תווים לכל היותר - למשל אות אחת שנוספה, חסרה או הוחלפה)
 *   - מילה שלמה מהשם שחסרה לגמרי בכותרת
 *   - מילה זרה שהוכנסה באמצע השם בכותרת
 * שם עם 0 שגיאות (התאמה מדויקת, כמו קודם) תמיד מנצח שם עם שגיאות; מעבר
 * לזה, פחות שגיאות עדיף, ובתיקו - יותר מילים ואז שם ארוך יותר, בדיוק כמו
 * בגרסה הקודמת. */

#define MAX_FUZZY_ERRORS 2          /* לא בשימוש יותר כתקרה קבועה - ראו maxErrorsForWordCount, שם התקרה גדלה עם מספר המילים בשם */
#define MAX_WORD_TYPO_DISTANCE 2    /* כמה תווים מותר שיבדילו בין שתי מילים כדי שעדיין ייחשבו "אותה מילה עם שגיאת הקלדה" */
#define FUZZY_INFINITY 1000

/* מרחק עריכה (Levenshtein) בין שתי מילים בודדות. יציאה מוקדמת כאשר הפרש
 * האורכים כבר עולה על הסף - מספיק בשביל לדעת שהמילים "לא קרובות", בלי
 * לחשב טבלת DP שלמה לחינם על מילים זרות לגמרי. */
static int wordEditDistance(const wchar_t *a, const wchar_t *b) {
    int la = (int)wcslen(a), lb = (int)wcslen(b);
    if (abs(la - lb) > MAX_WORD_TYPO_DISTANCE) return MAX_WORD_TYPO_DISTANCE + 1;
    static int dp[65][65];
    for (int i = 0; i <= la; i++) dp[i][0] = i;
    for (int j = 0; j <= lb; j++) dp[0][j] = j;
    for (int i = 1; i <= la; i++) {
        for (int j = 1; j <= lb; j++) {
            int cost = (a[i - 1] == b[j - 1]) ? 0 : 1;
            int del = dp[i - 1][j] + 1;
            int ins = dp[i][j - 1] + 1;
            int sub = dp[i - 1][j - 1] + cost;
            int m = del < ins ? del : ins;
            dp[i][j] = m < sub ? m : sub;
        }
    }
    return dp[la][lb];
}

static int wordSubstitutionCost(const wchar_t *a, const wchar_t *b) {
    if (wcscmp(a, b) == 0) return 0;               // זהות מדויקת - בלי שגיאה
    int d = wordEditDistance(a, b);
    return (d <= MAX_WORD_TYPO_DISTANCE) ? 1 : FUZZY_INFINITY; // "טעות הקלדה" קרובה = שגיאה אחת; אחרת - לא נחשב בכלל אותה מילה
}

/* התאמה מקורבת ברמת המילים, באותו רעיון של אלגוריתם חיפוש מחרוזת מקורבת
 * "עד k הבדלים" (כמו Ukkonen/agrep) - רק שכאן "התו" הוא מילה שלמה ולא
 * אות. pat = מילות שם הזמר (patN מילים), text = מילות הכותרת (textN
 * מילים). שורה 0 מאותחלת לאפס כדי לאפשר להתאמה להתחיל בכל נקודה בכותרת
 * בלי עונש - בדיוק כמו שהגרסה הקודמת בדקה כל start אפשרי. מחזיר את מספר
 * השגיאות המינימלי הדרוש כדי ליישר את כל שם הזמר עם קטע כלשהו בכותרת. */
static int fuzzyWordMatch(const wchar_t *const *text, int textN, const wchar_t *const *pat, int patN) {
    if (patN == 0 || textN == 0) return FUZZY_INFINITY;
    int prev[MAX_ARTIST_WORDS + 1];
    int cur[MAX_ARTIST_WORDS + 1];
    for (int i = 0; i <= patN; i++) prev[i] = i;

    int bestCost = FUZZY_INFINITY;
    for (int j = 1; j <= textN; j++) {
        cur[0] = 0; // התחלה חופשית - דילוג על מילות כותרת שלפני תחילת השם לא עולה כלום
        for (int i = 1; i <= patN; i++) {
            int sub = prev[i - 1] + wordSubstitutionCost(pat[i - 1], text[j - 1]);
            int del = prev[i] + 1;     // מילה מהשם חסרה בכותרת (למשל "בן")
            int ins = cur[i - 1] + 1;  // מילה זרה נדחסה בתוך הכותרת
            int m = sub < del ? sub : del;
            if (ins < m) m = ins;
            cur[i] = m;
        }
        if (cur[patN] < bestCost) bestCost = cur[patN];
        memcpy(prev, cur, sizeof(cur));
    }
    return bestCost;
}

/* Finds the known artist whose name appears in the song title, allowing up
 * to MAX_FUZZY_ERRORS small differences (typo inside a word, a missing
 * word, or an extra glued-on letter) - see the block comment above. When
 * more than one artist name matches, fewer errors wins first; ties break
 * the same way the old exact-match version did: more words, then a longer
 * name. Returns the index into ARTIST_LIST, or -1. */
/* עם רשימת זמרים גדולה (מאות ערכים) יש בה בהכרח גם הרבה שמות קצרים
 * וגנריים (מילה אחת/שתיים - למשל "ריטה", "כרמל", "בר"). אם היינו
 * מתירים להם את אותה טולרנטיות לשגיאות שניתנת לשם ארוך ומובחן, הם
 * היו "בולעים" כמעט כל תיקייה במקרה (כי קל מאוד למצוא מרחק עריכה קטן
 * למילה קצרה), ואז לא היה נשאר אף מועמד שדורש אישור ידני - למרות
 * שהרוב לא באמת זמר מוכר. לכן ככל שהשם קצר יותר (פחות מילים) - כך
 * דורשים ממנו התאמה מדויקת יותר. */
static int maxErrorsForWordCount(int awc) {
    if (awc <= 1) return 0;                  // מילה אחת: התאמה מדויקת בלבד
    return awc - 1;                          // שגיאת-אות אחת מותרת לכל מילה נוספת בשם (גדל עם אורך השם)
}

static int findArtistMatch(const wchar_t *title) {
    wchar_t words[MAX_TITLE_WORDS][64];
    int wc = tokenizeWords(title, words, MAX_TITLE_WORDS);
    if (wc == 0) return -1;

    const wchar_t *textPtrs[MAX_TITLE_WORDS];
    for (int i = 0; i < wc; i++) textPtrs[i] = words[i];

    int bestArtist = -1;
    int bestErrors = FUZZY_INFINITY;
    int bestWords = 0;
    size_t bestLen = 0;

    for (int a = 0; a < ARTIST_COUNT; a++) {
        int awc = artistWordCount[a];
        if (awc == 0) continue;
        int allowed = maxErrorsForWordCount(awc);
        if (awc > wc + allowed) continue; // אין סיכוי להצליח בתקציב השגיאות - חוסך זמן

        const wchar_t *patPtrs[MAX_ARTIST_WORDS];
        for (int k = 0; k < awc; k++) patPtrs[k] = artistWords[a][k];

        int errors = fuzzyWordMatch(textPtrs, wc, patPtrs, awc);
        if (errors > allowed) continue;

        size_t nameLen = wcslen(ARTIST_LIST[a]);
        if (errors < bestErrors ||
            (errors == bestErrors && (awc > bestWords ||
             (awc == bestWords && nameLen > bestLen)))) {
            bestArtist = a;
            bestErrors = errors;
            bestWords = awc;
            bestLen = nameLen;
        }
    }
    return bestArtist;
}


/* ============================ Gemini AI lookup ============================
 * Sends each song's filename/title to Google's Gemini API and asks it to
 * guess the artist and album (from its own knowledge / any info encoded in
 * the name - the API is not given the actual audio, only the text). This is
 * a best-effort text guess, not real audio recognition: a generic filename
 * with no useful hint will come back "unknown", and a wrong guess is
 * possible for ambiguous titles. Requires internet access and a Gemini API
 * key (entered by the user in the UI). */

/* UTF-8 encodes src and appends a JSON-escaped version of it to out (which
 * must have room - out is a char buffer, outCap in bytes). */
static void appendJsonEscapedUtf8(const wchar_t *src, char *out, size_t outCap, size_t *outLen) {
    char utf8[2048];
    int n = WideCharToMultiByte(CP_UTF8, 0, src, -1, utf8, (int)sizeof(utf8), NULL, NULL);
    if (n <= 0) return;
    for (int i = 0; i < n - 1 && *outLen < outCap - 2; i++) {
        unsigned char c = (unsigned char)utf8[i];
        if (c == L'"' || c == L'\\') { out[(*outLen)++] = '\\'; out[(*outLen)++] = (char)c; }
        else if (c == '\n') { out[(*outLen)++] = '\\'; out[(*outLen)++] = 'n'; }
        else if (c == '\r') { /* skip */ }
        else if (c < 0x20) { /* skip other control chars */ }
        else out[(*outLen)++] = (char)c;
    }
}

/* Appends the UTF-8 encoding of one Unicode codepoint to a char buffer. */
static void appendUtf8Codepoint(unsigned int cp, char *out, size_t outCap, size_t *outLen) {
    if (*outLen >= outCap - 4) return;
    if (cp < 0x80) {
        out[(*outLen)++] = (char)cp;
    } else if (cp < 0x800) {
        out[(*outLen)++] = (char)(0xC0 | (cp >> 6));
        out[(*outLen)++] = (char)(0x80 | (cp & 0x3F));
    } else {
        out[(*outLen)++] = (char)(0xE0 | (cp >> 12));
        out[(*outLen)++] = (char)(0x80 | ((cp >> 6) & 0x3F));
        out[(*outLen)++] = (char)(0x80 | (cp & 0x3F));
    }
}

/* Extracts the (JSON-unescaped, UTF-8) string value of "key":"..." from a
 * JSON blob. Handles \", \\, \n, \t, \/ and \uXXXX (BMP only - fine for
 * Hebrew/Latin artist/album names). Returns 1 if the key was found. */
/* Parses a JSON string value starting at/after a key match - *pp should
 * point anywhere before the value's opening quote (e.g. right after the
 * matched `"key"`); advances *pp past the closing quote on success. */
static int parseJsonStringValueAt(const char **pp, wchar_t *out, size_t outCap) {
    const char *p = *pp;
    p = strchr(p, ':');
    if (!p) { out[0] = 0; return 0; }
    p++;
    while (*p == ' ' || *p == '\t' || *p == '\n' || *p == '\r') p++;
    if (*p != '"') { out[0] = 0; return 0; }
    p++;

    char buf[1024];
    size_t bl = 0;
    while (*p && *p != '"' && bl < sizeof(buf) - 4) {
        if (*p == '\\' && p[1]) {
            p++;
            if (*p == 'n') { buf[bl++] = ' '; p++; }
            else if (*p == 't') { buf[bl++] = ' '; p++; }
            else if (*p == 'u' && isxdigit((unsigned char)p[1]) && isxdigit((unsigned char)p[2]) &&
                     isxdigit((unsigned char)p[3]) && isxdigit((unsigned char)p[4])) {
                unsigned int cp = 0;
                for (int k = 1; k <= 4; k++) {
                    char c = p[k];
                    cp <<= 4;
                    if (c >= '0' && c <= '9') cp |= (unsigned int)(c - '0');
                    else if (c >= 'a' && c <= 'f') cp |= (unsigned int)(c - 'a' + 10);
                    else if (c >= 'A' && c <= 'F') cp |= (unsigned int)(c - 'A' + 10);
                }
                appendUtf8Codepoint(cp, buf, sizeof(buf), &bl);
                p += 5;
            } else { buf[bl++] = *p; p++; }
        } else { buf[bl++] = *p; p++; }
    }
    if (*p != '"') { out[0] = 0; return 0; }
    buf[bl] = 0;
    p++; /* past closing quote */
    *pp = p;

    int wn = MultiByteToWideChar(CP_UTF8, 0, buf, -1, out, (int)outCap - 1);
    if (wn <= 0) { out[0] = 0; return 0; }
    return 1;
}

static int extractJsonStringField(const char *json, const char *key, wchar_t *out, size_t outCap) {
    char pattern[64];
    snprintf(pattern, sizeof(pattern), "\"%s\"", key);
    const char *p = strstr(json, pattern);
    if (!p) { out[0] = 0; return 0; }
    p += strlen(pattern);
    return parseJsonStringValueAt(&p, out, outCap);
}

#define AI_BATCH_SIZE 10

/* Sends one HTTPS POST request to the Gemini API asking it to guess the
 * artist/album for up to AI_BATCH_SIZE songs at once (one request instead
 * of one-per-song - much faster and uses far fewer API calls). fileNames/
 * titles are parallel arrays of length `count`; results are written into
 * the parallel outArtist/outAlbum arrays (each row is a 130-wchar_t buffer).
 * Returns the number of songs successfully parsed from the reply, in order
 * (0 if the request failed outright) - a short return means the model's
 * reply had fewer items than asked for; the caller treats the rest as
 * unidentified rather than misassigning results to the wrong song. */
static int queryGeminiArtistBatch(const wchar_t fileNames[][MAX_PATH], const wchar_t titles[][MAX_PATH],
                                   int count, const wchar_t *apiKey,
                                   wchar_t outArtist[][130], wchar_t outAlbum[][130]) {
    for (int i = 0; i < count; i++) { outArtist[i][0] = 0; outAlbum[i][0] = 0; }
    if (apiKey[0] == 0 || count <= 0) return 0;

    /* --- build the request body: one prompt listing all `count` songs --- */
    static char body[16384];
    size_t bl = 0;
    const char *prefix = "{\"contents\":[{\"parts\":[{\"text\":\"";
    memcpy(body, prefix, strlen(prefix)); bl = strlen(prefix);

    const char *instr =
        "You are helping organize a personal music library. Below is a "
        "numbered list of audio file names (and any title already guessed "
        "from the file) - you cannot hear the audio, only the text. For "
        "EACH numbered item, guess the most likely real-world artist and "
        "album. Reply with ONLY a single-line minified JSON array, no "
        "markdown, no extra text, with exactly one object per item IN THE "
        "SAME ORDER, shape: [{\\\"artist\\\":\\\"...\\\",\\\"album\\\":\\\"...\\\"},...]. "
        "If you cannot determine a field with reasonable confidence, use "
        "the string \\\"unknown\\\" for that field. Items:\\n";
    memcpy(body + bl, instr, strlen(instr)); bl += strlen(instr);

    for (int i = 0; i < count; i++) {
        char num[16];
        snprintf(num, sizeof(num), "%d. ", i + 1);
        memcpy(body + bl, num, strlen(num)); bl += strlen(num);
        appendJsonEscapedUtf8(fileNames[i], body, sizeof(body), &bl);
        const char *sep = " | title guess: ";
        memcpy(body + bl, sep, strlen(sep)); bl += strlen(sep);
        appendJsonEscapedUtf8(titles[i], body, sizeof(body), &bl);
        const char *nl = "\\n";
        memcpy(body + bl, nl, strlen(nl)); bl += strlen(nl);
    }

    const char *suffix = "\"}]}],\"generationConfig\":{\"temperature\":0,\"maxOutputTokens\":2048}}";
    memcpy(body + bl, suffix, strlen(suffix)); bl += strlen(suffix);
    body[bl] = 0;

    /* --- send it over WinHTTP --- */
    int parsed = 0;
    HINTERNET hSession = WinHttpOpen(L"SongOrganizer/1.0",
        WINHTTP_ACCESS_TYPE_DEFAULT_PROXY, WINHTTP_NO_PROXY_NAME, WINHTTP_NO_PROXY_BYPASS, 0);
    if (!hSession) return 0;
    WinHttpSetTimeouts(hSession, 8000, 8000, 30000, 30000);

    HINTERNET hConnect = WinHttpConnect(hSession, L"generativelanguage.googleapis.com",
        INTERNET_DEFAULT_HTTPS_PORT, 0);
    if (hConnect) {        wchar_t path[512];
        swprintf(path, 512, L"/v1beta/models/gemini-2.0-flash:generateContent?key=%ls", apiKey);
        HINTERNET hRequest = WinHttpOpenRequest(hConnect, L"POST", path, NULL,
            WINHTTP_NO_REFERER, WINHTTP_DEFAULT_ACCEPT_TYPES, WINHTTP_FLAG_SECURE);
        if (hRequest) {
            const wchar_t *headers = L"Content-Type: application/json\r\n";
            BOOL sent = WinHttpSendRequest(hRequest, headers, (DWORD)-1,
                body, (DWORD)bl, (DWORD)bl, 0);
            if (sent && WinHttpReceiveResponse(hRequest, NULL)) {
                static char resp[131072];
                size_t respLen = 0;
                DWORD avail = 0;
                while (WinHttpQueryDataAvailable(hRequest, &avail) && avail > 0) {
                    if (respLen + avail >= sizeof(resp)) avail = (DWORD)(sizeof(resp) - respLen - 1);
                    if (avail == 0) break;
                    DWORD read = 0;
                    if (!WinHttpReadData(hRequest, resp + respLen, avail, &read)) break;
                    respLen += read;
                    if (read == 0) break;
                }
                resp[respLen] = 0;

                /* candidates[0].content.parts[0].text holds our inner JSON
                 * array, itself JSON-escaped as a string - extract it, then
                 * walk through it pulling out "artist"/"album" pairs in
                 * order, one per song in the batch. */
                wchar_t innerTextW[8192];
                if (extractJsonStringField(resp, "text", innerTextW, 8192)) {
                    static char innerUtf8[16384];
                    WideCharToMultiByte(CP_UTF8, 0, innerTextW, -1, innerUtf8, (int)sizeof(innerUtf8), NULL, NULL);

                    const char *cursor = innerUtf8;
                    while (parsed < count) {
                        const char *artistKey = strstr(cursor, "\"artist\"");
                        if (!artistKey) break;
                        const char *p = artistKey + 8;
                        if (!parseJsonStringValueAt(&p, outArtist[parsed], 130)) break;
                        cursor = p;
                        const char *albumKey = strstr(cursor, "\"album\"");
                        if (!albumKey) break;
                        p = albumKey + 7;
                        if (!parseJsonStringValueAt(&p, outAlbum[parsed], 130)) break;
                        cursor = p;
                        parsed++;
                    }
                }
            }
            WinHttpCloseHandle(hRequest);
        }
        WinHttpCloseHandle(hConnect);
    }
    WinHttpCloseHandle(hSession);
    return parsed;
}

/* Dynamic (linear-scan) list of artist names discovered via the AI, since
 * unlike the fixed ARTIST_LIST we don't know how many distinct artists
 * there'll be ahead of time. Fine for realistic library sizes. */
typedef struct { wchar_t name[130]; int count; } AiArtistEntry;
static AiArtistEntry *aiArtists;
static int aiArtistCount = 0;

static int findOrAddAiArtist(const wchar_t *name) {
    for (int i = 0; i < aiArtistCount; i++)
        if (_wcsicmp(aiArtists[i].name, name) == 0) return i;
    wcsncpy(aiArtists[aiArtistCount].name, name, 129);
    aiArtists[aiArtistCount].name[129] = 0;
    aiArtists[aiArtistCount].count = 0;
    return aiArtistCount++;
}

/* Runs the "identify with AI" pipeline: for every scanned song, asks Gemini
 * to guess the artist (text-only guess from the filename/title - not real
 * audio recognition), then sorts into
 * <source>\כל השירים\זיהוי AI\זמרים מזוהים\<artist>\, mirroring the
 * known-artist-list pipeline above. Songs the API can't identify (or any
 * song hit by a network/API error) fall into \לא מזוהים\. */
static const wchar_t aiRootDirName[] = L"זיהוי AI";

static void runOrganizerByAI(const wchar_t *sourcePath, const wchar_t *destPath, int moveMode, const wchar_t *apiKey) {
    songCount = 0;
    copiedCount = 0; skippedDuplicateCount = 0; skippedByUserCount = 0; errorCount = 0;
    totalFilesSeen = 0; accessDeniedDirs = 0; sampleExtCount = 0;

    if (apiKey[0] == 0) {
        logLineW(L"שגיאה: לא הוזן מפתח API של Gemini. הכנס אותו בשדה שמופיע כשמצב הזיהוי ב-AI פעיל.");
        return;
    }

    logLineW(L"סורק קבצי שמע לזיהוי באמצעות AI (Gemini) ב-%ls ...", sourcePath);
    scanDir(sourcePath);
    logLineW(L"נמצאו %d קבצי שמע.", songCount);

    if (songCount == 0) {
        logLineW(L"אין מה לארגן.");
        return;
    }

    aiArtistCount = 0;

    wchar_t songsRoot[MAX_PATH];
    swprintf(songsRoot, MAX_PATH, L"%ls\\%ls", destPath, rootDirName);
    if (!CreateDirectoryW(songsRoot, NULL) && GetLastError() != ERROR_ALREADY_EXISTS) {
        DWORD err = GetLastError();
        logLineW(L"לא ניתן ליצור את תיקיית השורש '%ls' (קוד %d).", rootDirName, (int)err);
        errorCount++;
        return;
    }

    wchar_t aiRoot[MAX_PATH];
    swprintf(aiRoot, MAX_PATH, L"%ls\\%ls", songsRoot, aiRootDirName);
    if (!CreateDirectoryW(aiRoot, NULL) && GetLastError() != ERROR_ALREADY_EXISTS) {
        DWORD err = GetLastError();
        logLineW(L"לא ניתן ליצור את תיקיית '%ls' (קוד %d).", aiRootDirName, (int)err);
        errorCount++;
        return;
    }

    wchar_t identifiedRoot[MAX_PATH], unidentifiedRoot[MAX_PATH];
    swprintf(identifiedRoot, MAX_PATH, L"%ls\\%ls", aiRoot, identifiedRootDirName);
    swprintf(unidentifiedRoot, MAX_PATH, L"%ls\\%ls", aiRoot, unidentifiedDirName);
    CreateDirectoryW(identifiedRoot, NULL);
    CreateDirectoryW(unidentifiedRoot, NULL);

    logLineW(L"שולח שירים ל-Gemini לזיהוי אמן/אלבום, %d בכל בקשה...", AI_BATCH_SIZE);
    setProgress(0, songCount);
    setProgressFolders(0, songCount);
    setProgressOverall(0, songCount);
    int identifiedCount = 0, unidentifiedCount = 0, apiErrorCount = 0;

    static wchar_t batchFileNames[AI_BATCH_SIZE][MAX_PATH];
    static wchar_t batchTitles[AI_BATCH_SIZE][MAX_PATH];
    static wchar_t batchArtist[AI_BATCH_SIZE][130];
    static wchar_t batchAlbum[AI_BATCH_SIZE][130];

    for (int base = 0; base < songCount; base += AI_BATCH_SIZE) {
        int batchCount = songCount - base;
        if (batchCount > AI_BATCH_SIZE) batchCount = AI_BATCH_SIZE;

        for (int k = 0; k < batchCount; k++) {
            wcsncpy(batchFileNames[k], songs[base + k].fileName, MAX_PATH - 1);
            batchFileNames[k][MAX_PATH - 1] = 0;
            wcsncpy(batchTitles[k], songs[base + k].title, MAX_PATH - 1);
            batchTitles[k][MAX_PATH - 1] = 0;
        }

        wchar_t batchLabel[64];
        swprintf(batchLabel, 64, L"קבוצת %d-%d מתוך %d", base + 1, base + batchCount, songCount);
        setCurrentFile(batchLabel);

        int parsed = queryGeminiArtistBatch(batchFileNames, batchTitles, batchCount, apiKey,
                                             batchArtist, batchAlbum);
        if (parsed < batchCount) apiErrorCount += (batchCount - parsed);

        for (int k = 0; k < batchCount; k++) {
            int i = base + k;
            int ok = (k < parsed);
            wchar_t *aiArtist = batchArtist[k];

            wchar_t destDir[MAX_PATH];
            if (ok && aiArtist[0] && _wcsicmp(aiArtist, L"unknown") != 0) {
                sanitizeFileNameInPlace(aiArtist);
                int idx = findOrAddAiArtist(aiArtist);
                swprintf(destDir, MAX_PATH, L"%ls\\%ls", identifiedRoot, aiArtists[idx].name);
                if (aiArtists[idx].count == 0) {
                    if (!CreateDirectoryW(destDir, NULL) && GetLastError() != ERROR_ALREADY_EXISTS) {
                        DWORD err = GetLastError();
                        logLineW(L"  שגיאה ביצירת תיקיית '%ls' (קוד %d)", aiArtists[idx].name, (int)err);
                        errorCount++;
                    }
                }
                aiArtists[idx].count++;
            } else {
                wcsncpy(destDir, unidentifiedRoot, MAX_PATH - 1);
                destDir[MAX_PATH - 1] = 0;
            }

            wchar_t dest[MAX_PATH];
            int r = copyOrMove(songs[i].path, destDir, songs[i].fileName, moveMode, dest, MAX_PATH);
            if (r == 1) {
                copiedCount++;
                if (ok && aiArtist[0] && _wcsicmp(aiArtist, L"unknown") != 0) identifiedCount++;
                else unidentifiedCount++;
            } else if (r == -1) {
                logLineW(L"  דולג לפי בקשת המשתמש: %ls", songs[i].fileName);
                skippedByUserCount++;
            } else {
                DWORD err = GetLastError();
                logLineW(L"  שגיאה: %ls (קוד %d)", songs[i].fileName, (int)err);
                errorCount++;
            }
            setProgress(i + 1, songCount);
            setProgressFolders(i + 1, songCount);
            setProgressOverall(i + 1, songCount);
        }
    }
    setCurrentFile(NULL);

    for (int i = 0; i < aiArtistCount; i++)
        if (aiArtists[i].count > 0)
            logLineW(L"  %ls  -  %d שירים", aiArtists[i].name, aiArtists[i].count);

    logLineW(L"");
    logLineW(L"=== סיכום ===");
    logLineW(L"תיקייה: %ls", aiRoot);
    logLineW(L"סה\"כ קבצי שמע שנסרקו: %d", songCount);
    logLineW(L"זמרים שזוהו ע\"י AI: %d (סה\"כ %d שירים בתיקיית '%ls')", aiArtistCount, identifiedCount, identifiedRootDirName);
    logLineW(L"שירים שלא זוהו: %d (תיקיית '%ls')", unidentifiedCount, unidentifiedDirName);
    if (apiErrorCount > 0)
        logLineW(L"בקשות ל-Gemini שנכשלו (בעיית רשת/מפתח API): %d - שירים אלו הועברו ל'לא מזוהים'", apiErrorCount);
    if (skippedDuplicateCount > 0)
        logLineW(L"קבצים שדולגו כי כבר היו מאורגנים מריצה קודמת: %d", skippedDuplicateCount);
    if (skippedByUserCount > 0)
        logLineW(L"קבצים שדולגו ידנית (כפתור \"דלג\"): %d", skippedByUserCount);
    if (errorCount > 0) logLineW(L"שגיאות: %d", errorCount);
}

static int comparePairOrder(const void *pa, const void *pb) {
    int a = *(const int *)pa;
    int b = *(const int *)pb;
    return pairs[b].count - pairs[a].count;
}

/* Sorts indices of ungrouped songs by their origin folder name (case-
 * insensitive) so songs that came from the same source folder end up next
 * to each other and can be pulled out as a run. */
static int compareUngroupedByOrigin(const void *pa, const void *pb) {
    int a = *(const int *)pa;
    int b = *(const int *)pb;
    return _wcsicmp(songs[a].originDir, songs[b].originDir);
}

/* Runs the offline duplicate-grouping pipeline.
 * Known artist duplicates are routed automatically to the canonical artist
 * folder from ARTIST_LIST and never enter the review screen; duplicates whose
 * identifying phrase is not a known artist are presented for user approval.
 * logLineW/setProgress push updates to the UI thread. */
static void runOrganizer(const wchar_t *sourcePath, const wchar_t *destPath, int moveMode) {
    songCount = 0; pairCount = 0; nodePoolCount = 0;
    copiedCount = 0; skippedDuplicateCount = 0; skippedByUserCount = 0; errorCount = 0;
    totalFilesSeen = 0; accessDeniedDirs = 0; sampleExtCount = 0;
    memset(songPairCount_, 0, sizeof(songPairCount_));
    for (int i = 0; i < PAIR_HASH_SIZE; i++) pairHashTable[i] = -1;

    logLineW(L"סורק את כל הנתיב שנבחר ואת כל תתי-התיקיות לקבצי שמע...");
    scanDir(sourcePath);
    logLineW(L"נמצאו %d קבצי שמע.", songCount);
    if (songCount == 0) {
        logLineW(L"אין מה לארגן.");
        return;
    }

    /* 1) Complete scan + metadata indexing. No output classification folders
       are created before the review screen below. */
    buildPairIndex();
    buildArtistTokens();

    static int order[MAX_UNIQUE_PAIRS];
    static int pairAutoApproved[MAX_UNIQUE_PAIRS];
    static int pairKnownArtistIdx[MAX_UNIQUE_PAIRS];
    static int pairCandidateIdx[MAX_UNIQUE_PAIRS];
    for (int i = 0; i < pairCount; i++) {
        order[i] = i;
        pairAutoApproved[i] = 0;
        pairKnownArtistIdx[i] = -1;
        pairCandidateIdx[i] = -1;
    }
    qsort(order, pairCount, sizeof(int), comparePairOrder);

    /* 2) Repeated names/phrases that match a known artist are automatic.
       Every other repeated value/phrase goes to one review page. */
    candidatePairCount = 0;
    for (int oi = 0; oi < pairCount; oi++) {
        int w = order[oi];
        if (pairs[w].count < 2) continue;
        int knownArtistIdx = findArtistMatch(pairs[w].display);
        if (knownArtistIdx >= 0) {
            pairAutoApproved[w] = 1;
            pairKnownArtistIdx[w] = knownArtistIdx;
        } else if (candidatePairCount < MAX_UNIQUE_PAIRS) {
            CandidatePair *cp = &candidatePairs[candidatePairCount];
            wcsncpy(cp->name, pairs[w].display, 129);
            cp->name[129] = 0;
            cp->pairIndex = w;
            cp->songCount = pairs[w].count;
            cp->approved = 0; /* check = create folder; leave unchecked = אחר */
            pairCandidateIdx[w] = candidatePairCount++;
        }
    }

    if (candidatePairCount > 0) {
        g_reviewIsArtistMode = 0;
        logLineW(L"נמצאו %d כפילויות שאינן מזוהות כשמות זמרים מוכרים. בחר עכשיו אילו תיקיות ליצור.", candidatePairCount);
        ResetEvent(g_reviewDoneEvent);
        PostMessage(g_hMain, WM_APP_SHOW_REVIEW, 0, 0);
        WaitForSingleObject(g_reviewDoneEvent, INFINITE);
    }

    /* 3) Only after review do we start creating output folders. */
    swprintf(rootDir, MAX_PATH, L"%ls\\%ls", destPath, rootDirName);
    if (!CreateDirectoryW(rootDir, NULL) && GetLastError() != ERROR_ALREADY_EXISTS) {
        logLineW(L"לא ניתן ליצור את תיקיית השורש '%ls' (קוד %d).", rootDirName, (int)GetLastError());
        errorCount++;
        return;
    }

    wchar_t artistsRoot[MAX_PATH], alphabetRoot[MAX_PATH], otherRoot[MAX_PATH];
    swprintf(artistsRoot, MAX_PATH, L"%ls\\%ls", rootDir, artistsRootDirName);
    swprintf(otherRoot, MAX_PATH, L"%ls\\%ls", rootDir, L"אחר");
    if (!createOfflineAlphabetTree(rootDir, alphabetRoot, MAX_PATH)) {
        logLineW(L"לא ניתן ליצור את תיקיית '%ls'.", offlineAlphabetRootName);
        errorCount++;
        return;
    }

    /* 4) Final assignment. A song may match several duplicate candidates;
       an approved/automatic duplicate always wins over a rejected one, and
       among approved candidates the most repeated candidate wins. */
    static int finalPair[MAX_SONGS];
    static int hasRejectedDuplicate[MAX_SONGS];
    static int sortedIntoFolder[MAX_SONGS];
    for (int i = 0; i < songCount; i++) {
        finalPair[i] = -1;
        hasRejectedDuplicate[i] = 0;
        sortedIntoFolder[i] = 0;
    }

    for (int oi = 0; oi < pairCount; oi++) {
        int w = order[oi];
        if (pairs[w].count < 2) continue;
        int idx = pairCandidateIdx[w];
        int approved = pairAutoApproved[w] || (idx >= 0 && candidatePairs[idx].approved);
        for (int node = pairs[w].headNode; node != -1; node = nodePool[node].next) {
            int si = nodePool[node].songIndex;
            if (!approved) {
                hasRejectedDuplicate[si] = 1;
            } else if (finalPair[si] < 0 || pairs[w].count > pairs[finalPair[si]].count) {
                finalPair[si] = w;
            }
        }
    }

    setProgress(0, songCount);
    setProgressFolders(0, songCount);
    setProgressOverall(0, songCount);

    int copiedOrMoved = 0;
    int duplicateSorted = 0;
    int alphabetSorted = 0;
    int otherSorted = 0;
    int otherCreated = 0;
    int artistsRootCreated = 0;

    /* Approved/automatic duplicates. */
    for (int i = 0; i < songCount; i++) {
        int w = finalPair[i];
        if (w < 0) continue;

        wchar_t folderName[130];
        int candidateIdx = pairCandidateIdx[w];
        if (pairKnownArtistIdx[w] >= 0)
            wcsncpy(folderName, ARTIST_LIST[pairKnownArtistIdx[w]], 129);
        else if (candidateIdx >= 0)
            wcsncpy(folderName, candidatePairs[candidateIdx].name, 129);
        else
            wcsncpy(folderName, pairs[w].display, 129);
        folderName[129] = 0;
        sanitizeFileNameInPlace(folderName);

        if (!artistsRootCreated) {
            if (!CreateDirectoryW(artistsRoot, NULL) && GetLastError() != ERROR_ALREADY_EXISTS) {
                errorCount++;
                logLineW(L"שגיאה ביצירת '%ls' (קוד %d)", artistsRootDirName, (int)GetLastError());
                break;
            }
            artistsRootCreated = 1;
        }

        wchar_t groupDir[MAX_PATH];
        swprintf(groupDir, MAX_PATH, L"%ls\\%ls", artistsRoot, folderName);
        if (!CreateDirectoryW(groupDir, NULL) && GetLastError() != ERROR_ALREADY_EXISTS) {
            errorCount++;
            logLineW(L"שגיאה ביצירת תיקיית '%ls' (קוד %d)", folderName, (int)GetLastError());
            continue;
        }

        setCurrentFile(songs[i].title);
        int r;
        wchar_t movedDest[MAX_PATH];
        movedDest[0] = 0;
        if (moveMode)
            r = copyOrMove(songs[i].path, groupDir, songs[i].fileName, 1, movedDest, MAX_PATH);
        else
            r = copyIntoGroup(&songs[i], groupDir);
        if (r == 1) {
            if (moveMode) {
                wcsncpy(songs[i].path, movedDest, MAX_PATH - 1);
                songs[i].path[MAX_PATH - 1] = 0;
            }
            sortedIntoFolder[i] = 1;
            duplicateSorted++;
            copiedOrMoved++;
        } else if (r == -1) {
            skippedByUserCount++;
        } else {
            errorCount++;
        }
        setProgressFolders(i + 1, songCount);
        setProgress(i + 1, songCount);
        setProgressOverall(i + 1, songCount);
    }

    /* Rejected duplicate candidates go to one explicit "אחר" folder. */
    for (int i = 0; i < songCount; i++) {
        if (sortedIntoFolder[i] || !hasRejectedDuplicate[i]) continue;
        if (!otherCreated) {
            if (!CreateDirectoryW(otherRoot, NULL) && GetLastError() != ERROR_ALREADY_EXISTS) {
                errorCount++;
                logLineW(L"שגיאה ביצירת תיקיית 'אחר' (קוד %d)", (int)GetLastError());
                break;
            }
            otherCreated = 1;
        }
        setCurrentFile(songs[i].title);
        int r;
        wchar_t movedDest[MAX_PATH];
        movedDest[0] = 0;
        if (moveMode)
            r = copyOrMove(songs[i].path, otherRoot, songs[i].fileName, 1, movedDest, MAX_PATH);
        else
            r = copyIntoGroup(&songs[i], otherRoot);
        if (r == 1) {
            if (moveMode) {
                wcsncpy(songs[i].path, movedDest, MAX_PATH - 1);
                songs[i].path[MAX_PATH - 1] = 0;
            }
            sortedIntoFolder[i] = 1; otherSorted++; copiedOrMoved++;
        } else if (r == -1) skippedByUserCount++;
        else errorCount++;
        setProgressFolders(i + 1, songCount);
        setProgress(i + 1, songCount);
        setProgressOverall(i + 1, songCount);
    }

    /* No duplicate at all -> A-B sorting. */
    for (int i = 0; i < songCount; i++) {
        if (sortedIntoFolder[i]) continue;
        setCurrentFile(songs[i].title);
        wchar_t alphabetDir[MAX_PATH];
        offlineAlphabetDestination(alphabetRoot, songs[i].fileName, alphabetDir, MAX_PATH);
        if (!CreateDirectoryW(alphabetDir, NULL) && GetLastError() != ERROR_ALREADY_EXISTS) {
            errorCount++;
            continue;
        }
        int r;
        wchar_t movedDest[MAX_PATH];
        movedDest[0] = 0;
        if (moveMode)
            r = copyOrMove(songs[i].path, alphabetDir, songs[i].fileName, 1, movedDest, MAX_PATH);
        else
            r = copyIntoGroup(&songs[i], alphabetDir);
        if (r == 1) {
            if (moveMode) {
                wcsncpy(songs[i].path, movedDest, MAX_PATH - 1);
                songs[i].path[MAX_PATH - 1] = 0;
            }
            sortedIntoFolder[i] = 1; alphabetSorted++; copiedOrMoved++;
        } else if (r == -1) skippedByUserCount++;
        else errorCount++;
        setProgressFolders(i + 1, songCount);
        setProgress(i + 1, songCount);
        setProgressOverall(i + 1, songCount);
    }

    setCurrentFile(NULL);
    logLineW(L"");
    logLineW(L"=== סיכום ===");
    logLineW(L"תיקייה: %ls", rootDir);
    logLineW(L"סה\"כ קבצי שמע שנסרקו: %d", songCount);
    logLineW(L"שירים שסודרו לפי כפילויות/זמרים: %d", duplicateSorted);
    logLineW(L"שירים שכפילותם נדחתה ועברו ל'אחר': %d", otherSorted);
    logLineW(L"שירים ללא כפילות שסודרו לפי א-ב: %d", alphabetSorted);
    logLineW(L"סה\"כ הועתקו/הועברו: %d", copiedOrMoved);
    if (skippedDuplicateCount > 0)
        logLineW(L"כבר היו מסודרים ולכן דולגו: %d", skippedDuplicateCount);
    if (skippedByUserCount > 0)
        logLineW(L"דולגו ידנית: %d", skippedByUserCount);
    if (errorCount > 0)
        logLineW(L"שגיאות: %d", errorCount);
}

/* ============================= GUI layer ============================= */
/* Redesigned: light lavender canvas, white "card" panels with soft borders,
   an indigo gradient header, a pill-style segmented control for copy/move,
   and gradient-filled rounded buttons. Layout is computed once per resize
   in layoutCardRects() and reused both to position child controls and to
   paint the card backgrounds behind them. */

#pragma comment(lib, "msimg32.lib")

#define IDC_DRIVE_COMBO   1001
#define IDC_PATH_EDIT     1002
#define IDC_BROWSE_BTN    1003
#define IDC_COPY_RADIO    1004
#define IDC_MOVE_RADIO    1005
#define IDC_START_BTN     1006
#define IDC_LOG_EDIT      1007
#define IDC_PROGRESS      1008
#define IDC_GROUPBOX1     1009
#define IDC_GROUPBOX2     1010
#define IDC_LABEL1        1011
#define IDC_EXCLUDE_LIST      1012
#define IDC_EXCLUDE_ADD_BTN   1013
#define IDC_EXCLUDE_REMOVE_BTN 1014
#define IDC_EXCLUDE_LABEL     1015
#define IDC_SKIP_BTN          1016
#define IDC_CURRENT_LABEL     1017
#define IDC_PROGRESS_LABEL         1019
#define IDC_PROGRESS_FOLDERS       1020
#define IDC_PROGRESS_FOLDERS_LABEL 1021
#define IDC_PROGRESS_OVERALL       1022
#define IDC_PROGRESS_OVERALL_LABEL 1023
#define IDC_AI_CHECK          1024
#define IDC_API_KEY_EDIT      1025

#define WM_APP_LOGLINE   (WM_APP + 1)
#define WM_APP_PROGRESS  (WM_APP + 2)
#define WM_APP_DONE      (WM_APP + 3)
#define WM_APP_CURRENT   (WM_APP + 4)
#define WM_APP_PROGRESS_FOLDERS (WM_APP + 5)
#define WM_APP_PROGRESS_OVERALL (WM_APP + 6)

#define HEADER_H     80      /* Spacious header */
#define FOOTER_H     30      /* Thin footer disclaimer bar */
#define MARGIN       16      /* Generous margins */
#define CARD_GAP     18      /* Breathing room between elements */
#define CARD_RADIUS  16      /* Modern rounded corners */
#define BTN_RADIUS   24      /* Pill-shaped primary button */
#define MIN_COL_HEIGHT 520   /* none of the 3 dashboard columns gets shorter than
                                 this - if the window isn't tall enough to fit
                                 everything above this height, the body panel
                                 scrolls instead of clipping the bottom off
                                 (see g_hBody below) */
#define SCROLL_STEP  40      /* pixels moved per scrollbar arrow click / wheel notch */

/* Everything below the header (all five cards and their controls) lives
 * inside g_hBody, a child window with its own vertical scrollbar. This is
 * what used to be missing: the old version laid every card directly on the
 * main window with no scrolling at all, so on a short window (small
 * screen, non-maximized, high DPI scaling, or simply a user dragging it
 * smaller) the lower cards - the start button, and especially the log -
 * were silently clipped off the bottom with no way to reach them. Now the
 * body panel scrolls (mouse wheel, scrollbar, or dragging the thumb)
 * whenever the content is taller than the available space; it stays
 * unscrollable (and the scrollbar auto-hides) whenever everything already
 * fits, exactly like before. g_scrollY is how far the body's content is
 * scrolled up, in pixels. */
static HWND g_hBody;
static int g_scrollY = 0;

static HWND g_hDriveCombo, g_hPathEdit, g_hCopyRadio, g_hMoveRadio;
static HWND g_hReviewWnd, g_hReviewList, g_hReviewOkBtn, g_hReviewLabel;

static HWND g_hStartBtn, g_hLogEdit, g_hBrowseBtn;
/* the 3 native progress-bar controls were replaced by hand-drawn donut
   rings (see drawProgressRing / g_ringRect) - these 0-100 percentages are
   all that's left to track, updated wherever PBM_SETPOS used to be called. */
static int g_pctCopy = 0, g_pctFolders = 0, g_pctOverall = 0;
static HWND g_hExcludeList, g_hExcludeAddBtn, g_hExcludeRemoveBtn, g_hExcludeLabel;
static HWND g_hSrcLabel, g_hModeLabel, g_hCurrentLabel, g_hSkipBtn;
static HWND g_hAiCheck, g_hApiKeyEdit;
static HFONT g_hFont, g_hFontBold, g_hFontHeader, g_hFontSection, g_hFontSmall;
static HBRUSH g_hBrushBg, g_hBrushPanel;

/* ==== "Dashboard" THEME - light lavender-gray canvas with white cards, a
 * dark navy header/footer, and an orange primary accent, matching the
 * reference screenshot. ==== */
static COLORREF g_clrBg          = RGB(0xF3, 0xF5, 0xFA); /* Light lavender-gray canvas */
static COLORREF g_clrCard        = RGB(0xFF, 0xFF, 0xFF); /* White cards */
static COLORREF g_clrCardBorder  = RGB(0xE4, 0xE7, 0xF0); /* Soft gray-blue borders */
static COLORREF g_clrCardHover   = RGB(0xF7, 0xF8, 0xFC); /* Card hover state */
static COLORREF g_clrAccent      = RGB(0xF4, 0x7C, 0x20); /* Orange (primary accent) */
static COLORREF g_clrAccentDark  = RGB(0xD9, 0x63, 0x0C); /* Deep orange (pressed state) */
static COLORREF g_clrAccentLight = RGB(0xFD, 0xEC, 0xDD); /* Light orange bg */
static COLORREF g_clrHeaderTop   = RGB(0x1A, 0x28, 0x47); /* Dark navy header top */
static COLORREF g_clrHeaderBot   = RGB(0x26, 0x3B, 0x66); /* Dark navy header bottom */
static COLORREF g_clrText        = RGB(0x1C, 0x24, 0x33); /* Near-black text */
static COLORREF g_clrTextMuted   = RGB(0x8A, 0x93, 0xA6); /* Muted gray */
static COLORREF g_clrTextOnDark  = RGB(0xF3, 0xF6, 0xFD); /* High contrast white (on header/footer) */
static COLORREF g_clrBorder      = RGB(0xE4, 0xE7, 0xF0); /* Soft gray-blue borders */
static COLORREF g_clrWarn        = RGB(0xF4, 0x7C, 0x20); /* Orange (also used for warn/skip accents) */
static COLORREF g_clrSuccess     = RGB(0x22, 0xC7, 0x8C); /* Emerald green (success) */
static COLORREF g_clrWarnLight   = RGB(0xFD, 0xEC, 0xDD); /* Light orange bg */
static COLORREF g_clrShadow      = RGB(0xE1, 0xE4, 0xEE); /* Soft light-gray card shadow */

static int g_running = 0;
static int g_moveMode = 0; /* 0 = copy, 1 = move - drives the segmented control */
static int g_aiMode = 0; /* 1 = identify artist/album per song via the Gemini API instead */
static wchar_t g_apiKey[256] = L""; /* Gemini API key, entered by the user in the mode card */
static int g_animTick = 0;  /* Animation counter for smooth effects */
static UINT_PTR g_animTimer = 0; /* Animation timer ID */

typedef struct { wchar_t sourcePath[MAX_PATH]; wchar_t destPath[MAX_PATH]; int moveMode; int aiMode; wchar_t apiKey[256]; } WorkerArgs;


/* thread-safe log: format on caller thread, marshal a heap copy to the UI thread */
static void logLineW(const wchar_t *fmt, ...) {
    wchar_t buf[1024];
    va_list args;
    va_start(args, fmt);
    vswprintf(buf, 1024, fmt, args);
    va_end(args);
    wchar_t *copy = _wcsdup(buf);
    PostMessage(g_hMain, WM_APP_LOGLINE, 0, (LPARAM)copy);
}

static void setProgress(int value, int max) {
    PostMessage(g_hMain, WM_APP_PROGRESS, (WPARAM)value, (LPARAM)max);
}

/* Bar 2: "creating and sorting folders" - tracked separately from the copy
 * bar above so the phase after copying (which used to leave the single old
 * progress bar sitting motionless) shows its own visible progress. */
static void setProgressFolders(int value, int max) {
    PostMessage(g_hMain, WM_APP_PROGRESS_FOLDERS, (WPARAM)value, (LPARAM)max);
}

/* Bar 3: overall run progress, spanning every phase, so there's always one
 * bar that reads "how much of the whole run is left" regardless of which
 * phase is currently active. */
static void setProgressOverall(int value, int max) {
    PostMessage(g_hMain, WM_APP_PROGRESS_OVERALL, (WPARAM)value, (LPARAM)max);
}

/* Marshals "currently copying <title>" (or NULL to clear it) to the UI
 * thread. Called from the worker thread just before each file's copy/move
 * begins, so the on-screen label always reflects the file actually in
 * flight - the same file the skip button would abort. */
static void setCurrentFile(const wchar_t *title) {
    wchar_t *copy = title ? _wcsdup(title) : NULL;
    PostMessage(g_hMain, WM_APP_CURRENT, 0, (LPARAM)copy);
}

static DWORD WINAPI workerThread(LPVOID param) {

static DWORD WINAPI workerThread(LPVOID param) {
    WorkerArgs *args = (WorkerArgs *)param;
    if (args->aiMode) runOrganizerByAI(args->sourcePath, args->destPath, args->moveMode, args->apiKey);
    else runOrganizer(args->sourcePath, args->destPath, args->moveMode);
    free(args);
    PostMessage(g_hMain, WM_APP_DONE, 0, 0);
    return 0;
}

/* Populates the drive combo with removable/fixed drives, labeling each. */
static void populateDrives(HWND combo) {
    SendMessageW(combo, CB_RESETCONTENT, 0, 0);
    DWORD mask = GetLogicalDrives();
    for (int i = 0; i < 26; i++) {
        if (mask & (1 << i)) {
            wchar_t root[] = { (wchar_t)(L'A' + i), L':', L'\\', 0 };
            UINT type = GetDriveTypeW(root);
            const wchar_t *label =
                type == DRIVE_REMOVABLE ? L"נשלף - כרטיס/דיסק חיצוני" :
                type == DRIVE_FIXED     ? L"כונן קבוע" :
                type == DRIVE_CDROM     ? L"תקליטור" :
                type == DRIVE_REMOTE    ? L"רשת" : L"לא ידוע";
            wchar_t entry[64];
            swprintf(entry, 64, L"%ls   (%ls)", root, label);
            int idx = (int)SendMessageW(combo, CB_ADDSTRING, 0, (LPARAM)entry);
            SendMessageW(combo, CB_SETITEMDATA, idx, (LPARAM)_wcsdup(root));
        }
    }
    if (SendMessageW(combo, CB_GETCOUNT, 0, 0) > 0)
        SendMessageW(combo, CB_SETCURSEL, 0, 0);
}

static void appendLog(const wchar_t *line) {
    int len = GetWindowTextLengthW(g_hLogEdit);
    SendMessageW(g_hLogEdit, EM_SETSEL, len, len);
    SendMessageW(g_hLogEdit, EM_REPLACESEL, FALSE, (LPARAM)line);
    SendMessageW(g_hLogEdit, EM_REPLACESEL, FALSE, (LPARAM)L"\r\n");
    len = GetWindowTextLengthW(g_hLogEdit);
    SendMessageW(g_hLogEdit, EM_SETSEL, len, len);
    SendMessageW(g_hLogEdit, EM_SCROLLCARET, 0, 0);
}

/* Modern Explorer-style folder picker (drives, quick access, full window) -
   the same dialog Windows itself uses, instead of the old-style tree browser.
   Returns 1 and fills outPath if the user picked a folder, 0 if cancelled. */
static int pickFolder(HWND owner, const wchar_t *title, wchar_t *outPath, size_t outSize) {
    IFileOpenDialog *dlg = NULL;
    HRESULT hr = CoCreateInstance(&CLSID_FileOpenDialog, NULL, CLSCTX_INPROC_SERVER,
        &IID_IFileOpenDialog, (void **)&dlg);
    if (FAILED(hr) || !dlg) {
        // fallback to the legacy tree browser if the modern dialog is unavailable
        BROWSEINFOW bi = {0};
        wchar_t path[MAX_PATH] = L"";
        bi.hwndOwner = owner;
        bi.lpszTitle = title;
        bi.ulFlags = BIF_RETURNONLYFSDIRS | BIF_NEWDIALOGSTYLE | BIF_EDITBOX;
        PIDLIST_ABSOLUTE pidl = SHBrowseForFolderW(&bi);
        if (pidl) {
            int got = SHGetPathFromIDListW(pidl, path);
            CoTaskMemFree(pidl);
            if (got) {
                wcsncpy(outPath, path, outSize - 1);
                outPath[outSize - 1] = 0;
                return 1;
            }
        }
        return 0;
    }

    DWORD opts = 0;
    dlg->lpVtbl->GetOptions(dlg, &opts);
    dlg->lpVtbl->SetOptions(dlg, opts | FOS_PICKFOLDERS | FOS_FORCEFILESYSTEM | FOS_PATHMUSTEXIST);
    dlg->lpVtbl->SetTitle(dlg, title);

    int result = 0;
    hr = dlg->lpVtbl->Show(dlg, owner);
    if (SUCCEEDED(hr)) {
        IShellItem *item = NULL;
        hr = dlg->lpVtbl->GetResult(dlg, &item);
        if (SUCCEEDED(hr) && item) {
            PWSTR path = NULL;
            hr = item->lpVtbl->GetDisplayName(item, SIGDN_FILESYSPATH, &path);
            if (SUCCEEDED(hr) && path) {
                wcsncpy(outPath, path, outSize - 1);
                outPath[outSize - 1] = 0;
                result = 1;
                CoTaskMemFree(path);
            }
            item->lpVtbl->Release(item);
        }
    }
    dlg->lpVtbl->Release(dlg);
    return result;
}

static void browseForFolder(HWND owner) {
    wchar_t path[MAX_PATH];
    if (pickFolder(owner, L"בחר תיקייה או כונן לסריקה", path, MAX_PATH))
        SetWindowTextW(g_hPathEdit, path);
}

/* Opens the folder picker for an exclusion, and if a folder was chosen and
   isn't already in the list, adds it to both the exclude-dirs array (used by
   isPathExcluded during the scan) and the visible listbox. */
static void addExcludeFolder(HWND owner) {
    if (excludeDirCount >= MAX_EXCLUDE_DIRS) {
        MessageBoxW(owner, L"הגעת למספר המרבי של תיקיות מוחרגות.", L"שגיאה",
            MB_OK | MB_ICONWARNING | MB_RTLREADING);
        return;
    }
    wchar_t path[MAX_PATH];
    if (!pickFolder(owner, L"בחר תיקייה להחרגה מהסריקה", path, MAX_PATH)) return;

    size_t len = wcslen(path);
    while (len > 1 && path[len - 1] == L'\\') path[--len] = 0;

    for (int i = 0; i < excludeDirCount; i++) {
        if (_wcsicmp(excludeDirs[i], path) == 0) return; // already in the list
    }

    wcsncpy(excludeDirs[excludeDirCount], path, MAX_PATH - 1);
    excludeDirs[excludeDirCount][MAX_PATH - 1] = 0;
    excludeDirCount++;
    SendMessageW(g_hExcludeList, LB_ADDSTRING, 0, (LPARAM)path);
}

/* Removes the currently-selected item from the exclude listbox and its
   backing array, keeping both in sync. */
static void removeSelectedExcludeFolder(void) {
    int sel = (int)SendMessageW(g_hExcludeList, LB_GETCURSEL, 0, 0);
    if (sel == LB_ERR) return;

    for (int i = sel; i < excludeDirCount - 1; i++)
        wcscpy(excludeDirs[i], excludeDirs[i + 1]);
    excludeDirCount--;

    SendMessageW(g_hExcludeList, LB_DELETESTRING, sel, 0);
}

/* Fills a rounded rectangle with a vertical two-tone gradient, clipped to the
   rounded shape, then strokes a 1px border on top. Used for the header strip
   (radius 0) and for the primary action button (radius > 0). */
static void fillGradientRoundRect(HDC dc, RECT r, COLORREF top, COLORREF bottom, int radius) {
    HRGN rgn = radius > 0
        ? CreateRoundRectRgn(r.left, r.top, r.right + 1, r.bottom + 1, radius, radius)
        : CreateRectRgn(r.left, r.top, r.right, r.bottom);
    HRGN oldClip = CreateRectRgn(0, 0, 0, 0);
    int hadClip = GetClipRgn(dc, oldClip);
    SelectClipRgn(dc, rgn);

    TRIVERTEX vert[2];
    vert[0].x = r.left;  vert[0].y = r.top;
    vert[0].Red = (COLOR16)(GetRValue(top) << 8); vert[0].Green = (COLOR16)(GetGValue(top) << 8);
    vert[0].Blue = (COLOR16)(GetBValue(top) << 8); vert[0].Alpha = 0;
    vert[1].x = r.right; vert[1].y = r.bottom;
    vert[1].Red = (COLOR16)(GetRValue(bottom) << 8); vert[1].Green = (COLOR16)(GetGValue(bottom) << 8);
    vert[1].Blue = (COLOR16)(GetBValue(bottom) << 8); vert[1].Alpha = 0;
    GRADIENT_RECT gr = { 0, 1 };
    GradientFill(dc, vert, 2, &gr, 1, GRADIENT_FILL_RECT_V);

    SelectClipRgn(dc, hadClip == 1 ? oldClip : NULL);
    DeleteObject(oldClip);
    DeleteObject(rgn);
}

/* Draws a white rounded "card" with a subtle border and a faint offset
   shadow, used behind every logical section of the form. */
static void drawCard(HDC dc, RECT r) {
    RECT shadow = r;
    OffsetRect(&shadow, 0, 3);
    HBRUSH shadowBrush = CreateSolidBrush(g_clrShadow);
    HRGN shadowRgn = CreateRoundRectRgn(shadow.left, shadow.top, shadow.right + 1, shadow.bottom + 1, CARD_RADIUS, CARD_RADIUS);
    FillRgn(dc, shadowRgn, shadowBrush);
    DeleteObject(shadowRgn);
    DeleteObject(shadowBrush);

    HBRUSH fillBrush = CreateSolidBrush(g_clrCard);
    HPEN borderPen = CreatePen(PS_SOLID, 1, g_clrCardBorder);
    HBRUSH oldBrush = SelectObject(dc, fillBrush);
    HPEN oldPen = SelectObject(dc, borderPen);
    RoundRect(dc, r.left, r.top, r.right, r.bottom, CARD_RADIUS, CARD_RADIUS);
    SelectObject(dc, oldBrush);
    SelectObject(dc, oldPen);
    DeleteObject(fillBrush);
    DeleteObject(borderPen);
}

/* Custom-draw for the primary (accent, gradient-filled) action button. */
static void drawAccentButton(LPDRAWITEMSTRUCT dis, const wchar_t *text, int enabled) {
    HDC dc = dis->hDC;
    RECT r = dis->rcItem;
    int pressed = (dis->itemState & ODS_SELECTED) != 0;
    int disabled = !enabled || (dis->itemState & ODS_DISABLED) != 0;

    if (disabled) {
        HBRUSH brush = CreateSolidBrush(RGB(0xC9, 0xCB, 0xDA));
        HPEN pen = CreatePen(PS_SOLID, 1, RGB(0xC9, 0xCB, 0xDA));
        HBRUSH oldBrush = SelectObject(dc, brush);
        HPEN oldPen = SelectObject(dc, pen);
        RoundRect(dc, r.left, r.top, r.right, r.bottom, BTN_RADIUS, BTN_RADIUS);
        SelectObject(dc, oldBrush); SelectObject(dc, oldPen);
        DeleteObject(brush); DeleteObject(pen);
    } else if (pressed) {
        fillGradientRoundRect(dc, r, g_clrAccentDark, g_clrAccentDark, BTN_RADIUS);
    } else {
        fillGradientRoundRect(dc, r, RGB(0xFA, 0x9A, 0x44), g_clrAccent, BTN_RADIUS);
    }

    SetBkMode(dc, TRANSPARENT);
    SetTextColor(dc, RGB(0xFF, 0xFF, 0xFF));
    HFONT oldFont = SelectObject(dc, g_hFontBold);
    RECT tr = r;
    DrawTextW(dc, text, -1, &tr, DT_CENTER | DT_VCENTER | DT_SINGLELINE);
    SelectObject(dc, oldFont);
}

/* Custom-draw for flat/outlined secondary buttons (browse, add/remove exclude). */
static void drawSecondaryButton(LPDRAWITEMSTRUCT dis, const wchar_t *text) {
    HDC dc = dis->hDC;
    RECT r = dis->rcItem;
    int pressed = (dis->itemState & ODS_SELECTED) != 0;

    COLORREF fill = pressed ? g_clrAccentLight : g_clrCard;
    HBRUSH brush = CreateSolidBrush(fill);
    HPEN pen = CreatePen(PS_SOLID, 1, pressed ? g_clrAccent : g_clrBorder);
    HBRUSH oldBrush = SelectObject(dc, brush);
    HPEN oldPen = SelectObject(dc, pen);

    RoundRect(dc, r.left, r.top, r.right, r.bottom, BTN_RADIUS, BTN_RADIUS);

    SelectObject(dc, oldBrush);
    SelectObject(dc, oldPen);
    DeleteObject(brush);
    DeleteObject(pen);

    SetBkMode(dc, TRANSPARENT);
    SetTextColor(dc, pressed ? g_clrAccentDark : g_clrText);
    HFONT oldFont = SelectObject(dc, g_hFont);
    DrawTextW(dc, text, -1, &r, DT_CENTER | DT_VCENTER | DT_SINGLELINE);
    SelectObject(dc, oldFont);
}

/* Custom-draw for the skip button: an amber outline so it visually reads as
   a distinct, slightly cautionary action from the other secondary buttons.
   Only meaningfully clickable while a copy/move is actually running. */
static void drawSkipButton(LPDRAWITEMSTRUCT dis, const wchar_t *text, int enabled) {
    HDC dc = dis->hDC;
    RECT r = dis->rcItem;
    int pressed = (dis->itemState & ODS_SELECTED) != 0;

    COLORREF border = enabled ? g_clrWarn : g_clrBorder;
    COLORREF fill = !enabled ? g_clrCard : (pressed ? g_clrWarn : g_clrWarnLight);
    HBRUSH brush = CreateSolidBrush(fill);
    HPEN pen = CreatePen(PS_SOLID, 1, border);
    HBRUSH oldBrush = SelectObject(dc, brush);
    HPEN oldPen = SelectObject(dc, pen);
    RoundRect(dc, r.left, r.top, r.right, r.bottom, BTN_RADIUS, BTN_RADIUS);
    SelectObject(dc, oldBrush);
    SelectObject(dc, oldPen);
    DeleteObject(brush);
    DeleteObject(pen);

    SetBkMode(dc, TRANSPARENT);
    SetTextColor(dc, !enabled ? g_clrTextMuted : (pressed ? RGB(0xFF, 0xFF, 0xFF) : g_clrWarn));
    HFONT oldFont = SelectObject(dc, g_hFontBold);
    DrawTextW(dc, text, -1, &r, DT_CENTER | DT_VCENTER | DT_SINGLELINE);
    SelectObject(dc, oldFont);
}

/* Custom-draw for the copy/move segmented control: a single pill-shaped
   track with the active side filled in the accent color, replacing the two
   plain radio buttons from the old UI. */
static void drawSegmentButton(LPDRAWITEMSTRUCT dis, const wchar_t *text, int isActive) {
    HDC dc = dis->hDC;
    RECT r = dis->rcItem;

    if (isActive) {
        fillGradientRoundRect(dc, r, RGB(0xFA, 0x9A, 0x44), g_clrAccent, BTN_RADIUS - 2);
    } else {
        HBRUSH brush = CreateSolidBrush(g_clrAccentLight);
        HBRUSH oldBrush = SelectObject(dc, brush);
        HPEN pen = CreatePen(PS_SOLID, 1, g_clrAccentLight);
        HPEN oldPen = SelectObject(dc, pen);
        RoundRect(dc, r.left, r.top, r.right, r.bottom, BTN_RADIUS - 2, BTN_RADIUS - 2);
        SelectObject(dc, oldBrush); SelectObject(dc, oldPen);
        DeleteObject(brush); DeleteObject(pen);
    }

    SetBkMode(dc, TRANSPARENT);
    SetTextColor(dc, isActive ? RGB(0xFF, 0xFF, 0xFF) : g_clrAccentDark);
    HFONT oldFont = SelectObject(dc, isActive ? g_hFontBold : g_hFont);
    DrawTextW(dc, text, -1, &r, DT_CENTER | DT_VCENTER | DT_SINGLELINE);
    SelectObject(dc, oldFont);
}

/* Draws a circular "donut" progress ring: a light gray track circle, an
   arc overlaid on top in `color` sweeping clockwise from 12 o'clock for
   `pct` percent of the circle, the percentage as bold text in the middle,
   and `label` in small muted text just below the ring. Replaces the 3
   horizontal progress bars from the previous design. */
static void drawProgressRing(HDC dc, RECT r, int pct, COLORREF color, const wchar_t *label) {
    if (pct < 0) pct = 0;
    if (pct > 100) pct = 100;

    int cx = (r.left + r.right) / 2;
    int cy = (r.top + r.bottom) / 2;
    int radius = ((r.right - r.left) < (r.bottom - r.top) ? (r.right - r.left) : (r.bottom - r.top)) / 2;
    int thickness = radius / 5;
    if (thickness < 4) thickness = 4;
    int ringR = radius - thickness / 2 - 1;

    /* background track */
    HPEN trackPen = CreatePen(PS_SOLID, thickness, RGB(0xE7, 0xEA, 0xF2));
    HPEN oldPen = SelectObject(dc, trackPen);
    HBRUSH oldBrush = SelectObject(dc, GetStockObject(NULL_BRUSH));
    Ellipse(dc, cx - ringR, cy - ringR, cx + ringR, cy + ringR);

    /* progress arc, clockwise from 12 o'clock */
    if (pct > 0) {
        HPEN arcPen = CreatePen(PS_SOLID, thickness, color);
        SelectObject(dc, arcPen);
        if (pct >= 100) {
            Ellipse(dc, cx - ringR, cy - ringR, cx + ringR, cy + ringR);
        } else {
            double startAngle = 90.0; /* AngleArc: 0 = 3 o'clock, CCW positive */
            double sweep = -360.0 * pct / 100.0; /* negative = clockwise */
            MoveToEx(dc, cx, cy, NULL);
            AngleArc(dc, cx, cy, ringR, (float)startAngle, (float)sweep);
        }
        SelectObject(dc, oldPen);
        DeleteObject(arcPen);
    } else {
        SelectObject(dc, oldPen);
    }
    SelectObject(dc, oldBrush);
    DeleteObject(trackPen);

    /* percentage text, centered in the ring */
    SetBkMode(dc, TRANSPARENT);
    SetTextColor(dc, g_clrText);
    HFONT oldFont = SelectObject(dc, g_hFontBold);
    wchar_t pctText[16];
    swprintf(pctText, 16, L"%d%%", pct);
    RECT pctR = { cx - radius, cy - 10, cx + radius, cy + 10 };
    DrawTextW(dc, pctText, -1, &pctR, DT_CENTER | DT_VCENTER | DT_SINGLELINE);

    /* label below the ring */
    SetTextColor(dc, g_clrTextMuted);
    SelectObject(dc, g_hFontSmall);
    RECT labelR = { r.left - 12, r.bottom + 4, r.right + 12, r.bottom + 22 };
    DrawTextW(dc, label, -1, &labelR, DT_CENTER | DT_TOP | DT_WORDBREAK);
    SelectObject(dc, oldFont);
}

/* Computes the three dashboard-column rectangles (settings / process / log),
   left-to-right in screen order regardless of RTL text, from the current
   client size. Shared by layout and painting so the drawn cards always line
   up exactly with their controls. */
typedef struct {
    RECT source; /* left column  - "הגדרות תיקייה" (folder settings)   */
    RECT action; /* middle column - "תהליך ארגון" (organize process)   */
    RECT log;    /* right column  - "יומן סריקה מפורט" (detailed log)  */
} CardRects;

static void layoutControls(HWND body); /* forward decl - used by updateBodyScroll below, defined further down */

/* `body` is g_hBody (everything below the header), and scrollY is how far
 * that content is currently scrolled up (see g_scrollY) - subtracting it
 * from the starting y is the entire scrolling mechanism: every card just
 * slides up by that many pixels, and controls scrolled above the top of
 * the body or below its bottom are automatically clipped by Windows since
 * they're children of g_hBody, not of the main window (so they can never
 * spill over and paint on top of the fixed header - see g_hBody's comment). */
static CardRects computeCardRects(HWND body, int scrollY) {
    RECT rc; GetClientRect(body, &rc);
    int w = rc.right - rc.left, h = rc.bottom - rc.top;
    int y0 = CARD_GAP - scrollY;

    int colH = h - MARGIN - y0;
    if (colH < MIN_COL_HEIGHT) colH = MIN_COL_HEIGHT;
    int y1 = y0 + colH;

    int colW = (w - 2 * MARGIN - 2 * CARD_GAP) / 3;
    if (colW < 200) colW = 200;

    int xSettings = MARGIN;
    int xAction   = xSettings + colW + CARD_GAP;
    int xLog      = xAction + colW + CARD_GAP;
    int xLogRight = xLog + colW;
    /* the log column soaks up any leftover width from integer rounding, so
       it always reaches exactly to the right margin */
    int rightEdge = w - MARGIN;
    if (xLogRight < rightEdge) xLogRight = rightEdge;

    CardRects c;
    c.source = (RECT){ xSettings, y0, xAction - CARD_GAP, y1 };
    c.action = (RECT){ xAction,   y0, xLog - CARD_GAP,     y1 };
    c.log    = (RECT){ xLog,      y0, xLogRight,           y1 };
    return c;
}

/* Total height of the content if it were laid out at its natural minimum
 * (columns at MIN_COL_HEIGHT, no scroll offset applied) - independent of
 * how tall the body window currently is. This is exactly the height at
 * which a scrollbar first becomes necessary, so it's what the scroll range
 * is computed from. */
static int computeContentHeight(HWND body) {
    CardRects c = computeCardRects(body, 0);
    return (c.source.bottom - c.source.top) + CARD_GAP + MARGIN;
}

/* Recomputes the scrollbar range/position for g_hBody from the current
 * window size and content height, clamps g_scrollY to stay in range
 * (e.g. after the window grows and less scrolling is needed than before),
 * repositions every control to match, and optionally repaints. Called
 * whenever the body is resized or the user scrolls it. */
static void updateBodyScroll(HWND body, BOOL redraw) {
    RECT rc; GetClientRect(body, &rc);
    int avail = rc.bottom - rc.top;
    int content = computeContentHeight(body);
    int maxScroll = content - avail;
    if (maxScroll < 0) maxScroll = 0;
    if (g_scrollY > maxScroll) g_scrollY = maxScroll;
    if (g_scrollY < 0) g_scrollY = 0;

    SCROLLINFO si = { sizeof(si) };
    si.fMask = SIF_RANGE | SIF_PAGE | SIF_POS;
    si.nMin = 0;
    si.nMax = content > 0 ? content - 1 : 0;
    si.nPage = (UINT)(avail > 0 ? avail : 1);
    si.nPos = g_scrollY;
    SetScrollInfo(body, SB_VERT, &si, TRUE); /* range <= page auto-hides the scrollbar */

    layoutControls(body);
    if (redraw) InvalidateRect(body, NULL, TRUE);
}

/* Screen-space rectangles of the three progress rings in the middle
   ("תהליך ארגון") column, recomputed every layout pass and reused by the
   ring-drawing code in BodyWndProc's WM_PAINT so the drawn rings always
   line up with where layoutControls put them. */
static RECT g_ringRect[3];
/* Row/column title text, drawn directly onto the card background in
   BodyWndProc's WM_PAINT (not real controls) - matches the bold section
   headers ("הגדרות תיקייה" / "תהליך ארגון" / "יומן סריקה מפורט") in the
   reference design. */
static const wchar_t *g_cardTitleSettings = L"הגדרות תיקייה";
static const wchar_t *g_cardTitleAction   = L"תהליך ארגון";
static const wchar_t *g_cardTitleLog      = L"יומן סריקה מפורט";

static void layoutControls(HWND body) {
    CardRects c = computeCardRects(body, g_scrollY);
    int pad = 18;
    int titleH = 34; /* space reserved at the top of every card for its bold title */

    /* ============ left column: "הגדרות תיקייה" (folder settings) ============ */
    int sx = c.source.left + pad, sw = (c.source.right - c.source.left) - pad * 2;
    int sy = c.source.top + titleH;

    MoveWindow(g_hSrcLabel, sx, sy, sw, 18, TRUE);
    sy += 22;
    MoveWindow(g_hDriveCombo, sx, sy, sw, 26, TRUE);
    sy += 34;
    MoveWindow(g_hBrowseBtn, sx, sy, 108, 30, TRUE);
    MoveWindow(g_hPathEdit, sx + 118, sy + 2, sw - 118, 26, TRUE);
    sy += 44;

    MoveWindow(g_hExcludeLabel, sx, sy, sw, 18, TRUE);
    sy += 24;
    MoveWindow(g_hExcludeList, sx, sy, sw, 110, TRUE);
    sy += 118;
    MoveWindow(g_hExcludeRemoveBtn, sx, sy, 120, 28, TRUE);
    MoveWindow(g_hExcludeAddBtn, sx + 128, sy, sw - 128, 28, TRUE);
    sy += 44;

    MoveWindow(g_hModeLabel, sx, sy, sw, 18, TRUE);
    sy += 24;
    int segW = (sw - 8) / 2;
    MoveWindow(g_hMoveRadio, sx, sy, segW, 32, TRUE);
    MoveWindow(g_hCopyRadio, sx + segW + 8, sy, segW, 32, TRUE);
    sy += 40;
    MoveWindow(g_hAiCheck, sx, sy, sw, 30, TRUE);
    sy += 34;
    MoveWindow(g_hApiKeyEdit, sx, sy, sw, 26, TRUE);

    /* ============ middle column: "תהליך ארגון" (organize process) ============ */
    int ax = c.action.left + pad, aw = (c.action.right - c.action.left) - pad * 2;
    int ay = c.action.top + titleH + 8;

    /* big pill-shaped primary action button */
    MoveWindow(g_hStartBtn, ax, ay, aw, 48, TRUE);
    ay += 60;

    /* status pill (current file) + the skip button, side by side */
    MoveWindow(g_hSkipBtn, ax, ay, 92, 32, TRUE);
    MoveWindow(g_hCurrentLabel, ax + 92 + 10, ay, aw - 92 - 10, 32, TRUE);
    ay += 48;

    /* three progress rings, side by side, each with its own label below it -
       positions cached in g_ringRect[] for BodyWndProc's WM_PAINT to draw */
    int ringGap = 14;
    int ringSize = (aw - ringGap * 2) / 3;
    if (ringSize > 96) ringSize = 96;
    int ringsW = ringSize * 3 + ringGap * 2;
    int ringsX = ax + (aw - ringsW) / 2;
    for (int i = 0; i < 3; i++) {
        int rx = ringsX + i * (ringSize + ringGap);
        g_ringRect[i] = (RECT){ rx, ay, rx + ringSize, ay + ringSize };
    }
    /* ============ right column: "יומן סריקה מפורט" (detailed scan log) ============ */
    int lx = c.log.left + pad, lw = (c.log.right - c.log.left) - pad * 2;
    int ly = c.log.top + titleH;
    MoveWindow(g_hLogEdit, lx, ly, lw, (c.log.bottom - pad) - ly, TRUE);
}

/* Mouse-wheel routing fix: Windows delivers WM_MOUSEWHEEL to whichever
 * control is under the cursor, not to g_hBody. Every button, label, combo
 * box, and edit field sitting on top of the scrollable page would
 * therefore just swallow the wheel and do nothing with it (or, in the case
 * of the log box / exclude list, scroll their own tiny internal content
 * instead of the page) - which in practice meant the only way to reach
 * anything below the fold was to grab the thin scrollbar thumb exactly, or
 * shrink-and-grow the window until it happened to fit. This subclass makes
 * every child of g_hBody forward the wheel to the page instead, so
 * scrolling works the same no matter where the mouse happens to be - the
 * actual fix for content being unreachable at the bottom. */
static LRESULT CALLBACK ChildWheelSubclassProc(HWND hwnd, UINT msg, WPARAM wp, LPARAM lp,
                                                UINT_PTR idSubclass, DWORD_PTR refData) {
    (void)idSubclass; (void)refData;
    if (msg == WM_MOUSEWHEEL) {
        return SendMessageW(g_hBody, WM_MOUSEWHEEL, wp, lp);
    }
    if (msg == WM_NCDESTROY) {
        RemoveWindowSubclass(hwnd, ChildWheelSubclassProc, 1);
    }
    return DefSubclassProc(hwnd, msg, wp, lp);
}

static LRESULT CALLBACK WndProc(HWND hwnd, UINT msg, WPARAM wp, LPARAM lp) {
    switch (msg) {
    case WM_CREATE: {
        /* Animation timer removed on request: it forced a full-window
           repaint every 50ms (20x/sec) for a tick counter (g_animTick) that
           no drawing code even used - so all it did was make the screen
           redraw constantly, which read as flicker. Nothing below moves on
           its own now; WM_PAINT only fires when something actually changes
           (resize, state change, etc.). */
        g_hBrushBg = CreateSolidBrush(g_clrBg);
        g_hBrushPanel = CreateSolidBrush(g_clrCard);

        /* The scrollable body panel - everything below the header lives
           inside it (see g_hBody's declaration comment above). Sized to
           fill whatever space is below the header right now; WM_SIZE keeps
           it in sync with the main window from here on. */
        {
            RECT rc0; GetClientRect(hwnd, &rc0);
            int bodyH = (rc0.bottom - rc0.top) - HEADER_H - FOOTER_H;
            if (bodyH < 0) bodyH = 0;
            g_hBody = CreateWindowExW(WS_EX_RTLREADING, L"SongOrganizerBodyWnd", NULL,
                WS_CHILD | WS_VISIBLE | WS_VSCROLL | WS_CLIPCHILDREN,
                0, HEADER_H, rc0.right - rc0.left, bodyH,
                hwnd, NULL, NULL, NULL);
        }

        g_hFont = CreateFontW(-15, 0, 0, 0, FW_NORMAL, 0, 0, 0,
            HEBREW_CHARSET, OUT_DEFAULT_PRECIS, CLIP_DEFAULT_PRECIS,
            CLEARTYPE_QUALITY, DEFAULT_PITCH | FF_DONTCARE, L"Segoe UI");
        g_hFontBold = CreateFontW(-15, 0, 0, 0, FW_BOLD, 0, 0, 0,
            HEBREW_CHARSET, OUT_DEFAULT_PRECIS, CLIP_DEFAULT_PRECIS,
            CLEARTYPE_QUALITY, DEFAULT_PITCH | FF_DONTCARE, L"Segoe UI");
        g_hFontHeader = CreateFontW(-24, 0, 0, 0, FW_BOLD, 0, 0, 0,
            HEBREW_CHARSET, OUT_DEFAULT_PRECIS, CLIP_DEFAULT_PRECIS,
            CLEARTYPE_QUALITY, DEFAULT_PITCH | FF_DONTCARE, L"Segoe UI");
        g_hFontSection = CreateFontW(-15, 0, 0, 0, FW_SEMIBOLD, 0, 0, 0,
            HEBREW_CHARSET, OUT_DEFAULT_PRECIS, CLIP_DEFAULT_PRECIS,
            CLEARTYPE_QUALITY, DEFAULT_PITCH | FF_DONTCARE, L"Segoe UI");
        g_hFontSmall = CreateFontW(-12, 0, 0, 0, FW_NORMAL, 0, 0, 0,
            HEBREW_CHARSET, OUT_DEFAULT_PRECIS, CLIP_DEFAULT_PRECIS,
            CLEARTYPE_QUALITY, DEFAULT_PITCH | FF_DONTCARE, L"Segoe UI");

        DWORD rtl = WS_EX_RTLREADING | WS_EX_RIGHT;

        g_hSrcLabel = CreateWindowExW(rtl, L"STATIC", L"בחר כונן / תיקייה לסריקה",
            WS_CHILD | WS_VISIBLE | SS_RIGHT, 0, 0, 0, 0, g_hBody, NULL, NULL, NULL);

        g_hDriveCombo = CreateWindowExW(rtl, L"COMBOBOX", NULL,
            WS_CHILD | WS_VISIBLE | CBS_DROPDOWNLIST | WS_VSCROLL,
            0, 0, 0, 200, g_hBody, (HMENU)IDC_DRIVE_COMBO, NULL, NULL);

        g_hBrowseBtn = CreateWindowExW(0, L"BUTTON", L"בחר תיקייה...",
            WS_CHILD | WS_VISIBLE | BS_OWNERDRAW,
            0, 0, 0, 0, g_hBody, (HMENU)IDC_BROWSE_BTN, NULL, NULL);

        g_hPathEdit = CreateWindowExW(rtl | WS_EX_CLIENTEDGE, L"EDIT", NULL,
            WS_CHILD | WS_VISIBLE | ES_AUTOHSCROLL,
            0, 0, 0, 0, g_hBody, (HMENU)IDC_PATH_EDIT, NULL, NULL);

        g_hModeLabel = CreateWindowExW(rtl, L"STATIC", L"מצב פעולה",
            WS_CHILD | WS_VISIBLE | SS_RIGHT, 0, 0, 0, 0, g_hBody, NULL, NULL, NULL);

        /* segmented pill control (was: two BS_AUTORADIOBUTTON) */
        g_hCopyRadio = CreateWindowExW(0, L"BUTTON", L"העתקה (השאר מקור)",
            WS_CHILD | WS_VISIBLE | BS_OWNERDRAW,
            0, 0, 0, 0, g_hBody, (HMENU)IDC_COPY_RADIO, NULL, NULL);
        g_hMoveRadio = CreateWindowExW(0, L"BUTTON", L"העברה (מחק מקור)",
            WS_CHILD | WS_VISIBLE | BS_OWNERDRAW,
            0, 0, 0, 0, g_hBody, (HMENU)IDC_MOVE_RADIO, NULL, NULL);

        g_hAiCheck = CreateWindowExW(0, L"BUTTON", L"זהה אמן ואלבום עם בינה מלאכותית (Gemini)",
            WS_CHILD | WS_VISIBLE | BS_OWNERDRAW,
            0, 0, 0, 0, g_hBody, (HMENU)IDC_AI_CHECK, NULL, NULL);

        g_hApiKeyEdit = CreateWindowExW(rtl | WS_EX_CLIENTEDGE, L"EDIT", NULL,
            WS_CHILD | WS_VISIBLE | ES_AUTOHSCROLL | ES_PASSWORD,
            0, 0, 0, 0, g_hBody, (HMENU)IDC_API_KEY_EDIT, NULL, NULL);
        SendMessageW(g_hApiKeyEdit, EM_SETCUEBANNER, TRUE, (LPARAM)L"מפתח API של Gemini");

        g_hExcludeLabel = CreateWindowExW(rtl, L"STATIC", L"תיקיות מוחרגות מהסריקה (לא ייספרו ולא יועתקו)",
            WS_CHILD | WS_VISIBLE | SS_RIGHT, 0, 0, 0, 0, g_hBody, (HMENU)IDC_EXCLUDE_LABEL, NULL, NULL);

        g_hExcludeList = CreateWindowExW(rtl | WS_EX_CLIENTEDGE, L"LISTBOX", NULL,
            WS_CHILD | WS_VISIBLE | LBS_NOTIFY | WS_VSCROLL,
            0, 0, 0, 0, g_hBody, (HMENU)IDC_EXCLUDE_LIST, NULL, NULL);

        g_hExcludeAddBtn = CreateWindowExW(0, L"BUTTON", L"הוסף תיקייה להחרגה...",
            WS_CHILD | WS_VISIBLE | BS_OWNERDRAW,
            0, 0, 0, 0, g_hBody, (HMENU)IDC_EXCLUDE_ADD_BTN, NULL, NULL);

        g_hExcludeRemoveBtn = CreateWindowExW(0, L"BUTTON", L"הסר נבחרת",
            WS_CHILD | WS_VISIBLE | BS_OWNERDRAW,
            0, 0, 0, 0, g_hBody, (HMENU)IDC_EXCLUDE_REMOVE_BTN, NULL, NULL);

        g_hStartBtn = CreateWindowExW(0, L"BUTTON", L"התחל ארגון שירים",
            WS_CHILD | WS_VISIBLE | BS_OWNERDRAW,
            0, 0, 0, 0, g_hBody, (HMENU)IDC_START_BTN, NULL, NULL);

        g_hSkipBtn = CreateWindowExW(0, L"BUTTON", L"דלג לשיר הבא",
            WS_CHILD | WS_VISIBLE | BS_OWNERDRAW | WS_DISABLED,
            0, 0, 0, 0, g_hBody, (HMENU)IDC_SKIP_BTN, NULL, NULL);

        DWORD rtl2 = WS_EX_RTLREADING | WS_EX_RIGHT;
        g_hCurrentLabel = CreateWindowExW(rtl2, L"STATIC", L"אין פעולה פעילה כרגע",
            WS_CHILD | WS_VISIBLE | SS_RIGHT | SS_ENDELLIPSIS, 0, 0, 0, 0, g_hBody, (HMENU)IDC_CURRENT_LABEL, NULL, NULL);

        /* the 3 progress bars are now hand-drawn donut rings (drawProgressRing),
           painted directly in BodyWndProc's WM_PAINT - no controls to create here. */

        g_hLogEdit = CreateWindowExW(rtl | WS_EX_CLIENTEDGE, L"EDIT", NULL,
            WS_CHILD | WS_VISIBLE | ES_MULTILINE | ES_READONLY | ES_AUTOVSCROLL |
            WS_VSCROLL | ES_LEFT,
            0, 0, 0, 0, g_hBody, (HMENU)IDC_LOG_EDIT, NULL, NULL);

        HWND bodyCtrls[] = { g_hDriveCombo, g_hBrowseBtn, g_hPathEdit, g_hLogEdit,
                       g_hExcludeList, g_hExcludeAddBtn, g_hExcludeRemoveBtn, g_hCurrentLabel };
        for (size_t i = 0; i < sizeof(bodyCtrls)/sizeof(bodyCtrls[0]); i++)
            SendMessageW(bodyCtrls[i], WM_SETFONT, (WPARAM)g_hFont, TRUE);
        SendMessageW(g_hSrcLabel, WM_SETFONT, (WPARAM)g_hFontSection, TRUE);
        SendMessageW(g_hModeLabel, WM_SETFONT, (WPARAM)g_hFontSection, TRUE);
        SendMessageW(g_hExcludeLabel, WM_SETFONT, (WPARAM)g_hFontSection, TRUE);

        /* every control that sits on the scrollable page needs the wheel
           forwarded to g_hBody - see ChildWheelSubclassProc above */
        HWND wheelCtrls[] = { g_hSrcLabel, g_hDriveCombo, g_hBrowseBtn, g_hPathEdit,
                       g_hModeLabel, g_hCopyRadio, g_hMoveRadio, g_hAiCheck,
                       g_hExcludeLabel, g_hExcludeList, g_hExcludeAddBtn, g_hExcludeRemoveBtn,
                       g_hStartBtn, g_hSkipBtn, g_hCurrentLabel, g_hLogEdit };
        for (size_t i = 0; i < sizeof(wheelCtrls)/sizeof(wheelCtrls[0]); i++)
            SetWindowSubclass(wheelCtrls[i], ChildWheelSubclassProc, 1, 0);

        g_moveMode = 0;
        populateDrives(g_hDriveCombo);

        updateBodyScroll(g_hBody, FALSE);
        return 0;
    }

    case WM_SIZE: {
        /* Only the header is drawn directly by the main window; everything
           else just needs g_hBody resized to fill the remaining space -
           g_hBody's own WM_SIZE (below, in BodyWndProc) takes it from
           there: recomputing the scroll range and repositioning every
           control so nothing ends up clipped off the bottom. */
        RECT rc; GetClientRect(hwnd, &rc);
        int w = rc.right - rc.left;
        int bodyH = (rc.bottom - rc.top) - HEADER_H - FOOTER_H;
        if (bodyH < 0) bodyH = 0;
        if (g_hBody) MoveWindow(g_hBody, 0, HEADER_H, w, bodyH, TRUE);
        InvalidateRect(hwnd, NULL, TRUE);
        return 0;
    }

    case WM_CTLCOLORSTATIC: {
        HDC dc = (HDC)wp;
        HWND ctl = (HWND)lp;
        SetTextColor(dc, (ctl == g_hCurrentLabel) ? g_clrTextMuted : g_clrText);
        /* labels sit directly on white cards; everything else sits on the canvas */
        if (ctl == g_hSrcLabel || ctl == g_hModeLabel || ctl == g_hExcludeLabel || ctl == g_hCurrentLabel) {
            SetBkColor(dc, g_clrCard);
            return (LRESULT)g_hBrushPanel;
        }
        SetBkColor(dc, g_clrBg);
        return (LRESULT)g_hBrushBg;
    }
    case WM_CTLCOLOREDIT: {
        HDC dc = (HDC)wp;
        SetTextColor(dc, g_clrText);
        SetBkColor(dc, g_clrCard);
        return (LRESULT)g_hBrushPanel;
    }
    case WM_CTLCOLORLISTBOX: {
        HDC dc = (HDC)wp;
        SetTextColor(dc, g_clrText);
        SetBkColor(dc, g_clrCard);
        return (LRESULT)g_hBrushPanel;
    }
    case WM_ERASEBKGND:
        /* No-op: WM_PAINT below always repaints the entire client area itself
           (via the off-screen buffer), so letting the default/GDI erase run
           here as well just means every frame is drawn twice - once by the
           erase fill, once by the real paint - which is what produced the
           visible flicker at the 20 FPS animation tick. */
        return 1;

    case WM_PAINT: {
        PAINTSTRUCT ps;
        HDC screenDc = BeginPaint(hwnd, &ps);

        RECT rc; GetClientRect(hwnd, &rc);
        int w = rc.right - rc.left;
        int h = rc.bottom - rc.top;
        if (w < 1) w = 1;
        if (h < 1) h = 1;

        /* Double buffering: draw the whole frame into an off-screen bitmap
           first, then copy it to the screen in one BitBlt. This is what
           actually stops the flicker - without it, the screen briefly shows
           the raw background before each shape gets drawn over it, which
           flashes every time the animation timer forces a repaint. */
        HDC dc = CreateCompatibleDC(screenDc);
        HBITMAP bmp = CreateCompatibleBitmap(screenDc, w, h);
        HBITMAP oldBmp = (HBITMAP)SelectObject(dc, bmp);

        FillRect(dc, &rc, g_hBrushBg);

        RECT header = { 0, 0, rc.right, HEADER_H };
        fillGradientRoundRect(dc, header, g_clrHeaderTop, g_clrHeaderBot, 0);

        SetBkMode(dc, TRANSPARENT);
        SetTextColor(dc, g_clrTextOnDark);
        HFONT oldFont = SelectObject(dc, g_hFontHeader);
        RECT titleR = { MARGIN, 12, rc.right - MARGIN, 42 };
        DrawTextW(dc, L"מארגן שירים", -1, &titleR, DT_RIGHT | DT_VCENTER | DT_SINGLELINE);
        SelectObject(dc, g_hFontSmall);
        RECT subR = { MARGIN, 44, rc.right - MARGIN, 66 };
        DrawTextW(dc, L"סידור וקיבוץ אוטומטי של קבצי שמע לפי שם", -1, &subR, DT_RIGHT | DT_VCENTER | DT_SINGLELINE);
        SelectObject(dc, oldFont);
        /* The cards themselves are drawn by g_hBody's own WM_PAINT now
           (BodyWndProc, below) - it has its own client coordinate space,
           which is what makes scrolling them just a matter of subtracting
           g_scrollY in computeCardRects. */

        /* thin dark footer disclaimer bar, pinned to the bottom of the window */
        RECT footer = { 0, rc.bottom - FOOTER_H, rc.right, rc.bottom };
        fillGradientRoundRect(dc, footer, g_clrHeaderTop, g_clrHeaderTop, 0);
        SetBkMode(dc, TRANSPARENT);
        SetTextColor(dc, g_clrTextMuted);
        HFONT oldFooterFont = SelectObject(dc, g_hFontSmall);
        DrawTextW(dc, L"נרשם ונפתח ע\"י חייא שיאומי ממתמחים טופ", -1, &footer, DT_CENTER | DT_VCENTER | DT_SINGLELINE);
        SelectObject(dc, oldFooterFont);

        BitBlt(screenDc, 0, 0, w, h, dc, 0, 0, SRCCOPY);

        SelectObject(dc, oldBmp);
        DeleteObject(bmp);
        DeleteDC(dc);

        EndPaint(hwnd, &ps);
        return 0;
    }

    case WM_DRAWITEM: {
        LPDRAWITEMSTRUCT dis = (LPDRAWITEMSTRUCT)lp;
        if (dis->CtlID == IDC_START_BTN) {
            wchar_t text[64];
            GetWindowTextW(dis->hwndItem, text, 64);
            drawAccentButton(dis, text, !g_running);
            return TRUE;
        } else if (dis->CtlID == IDC_BROWSE_BTN || dis->CtlID == IDC_EXCLUDE_ADD_BTN ||
                   dis->CtlID == IDC_EXCLUDE_REMOVE_BTN) {
            wchar_t text[64];
            GetWindowTextW(dis->hwndItem, text, 64);
            drawSecondaryButton(dis, text);
            return TRUE;
        } else if (dis->CtlID == IDC_COPY_RADIO) {
            drawSegmentButton(dis, L"העתקה (השאר מקור)", g_moveMode == 0);
            return TRUE;
        } else if (dis->CtlID == IDC_MOVE_RADIO) {
            drawSegmentButton(dis, L"העברה (מחק מקור)", g_moveMode == 1);
            return TRUE;
        } else if (dis->CtlID == IDC_AI_CHECK) {
            drawSegmentButton(dis, L"זהה אמן ואלבום עם בינה מלאכותית (Gemini)", g_aiMode == 1);
            return TRUE;
        } else if (dis->CtlID == IDC_SKIP_BTN) {
            wchar_t text[64];
            GetWindowTextW(dis->hwndItem, text, 64);
            drawSkipButton(dis, text, g_running);
            return TRUE;
        }
        return FALSE;
    }

    case WM_COMMAND: {
        int id = LOWORD(wp);
        if (id == IDC_BROWSE_BTN && HIWORD(wp) == BN_CLICKED) {
            browseForFolder(hwnd);
        } else if (id == IDC_EXCLUDE_ADD_BTN && HIWORD(wp) == BN_CLICKED) {
            if (!g_running) addExcludeFolder(hwnd);
        } else if (id == IDC_EXCLUDE_REMOVE_BTN && HIWORD(wp) == BN_CLICKED) {
            if (!g_running) removeSelectedExcludeFolder();
        } else if (id == IDC_COPY_RADIO && HIWORD(wp) == BN_CLICKED) {
            if (g_moveMode != 0) { g_moveMode = 0; InvalidateRect(g_hCopyRadio, NULL, TRUE); InvalidateRect(g_hMoveRadio, NULL, TRUE); }
        } else if (id == IDC_MOVE_RADIO && HIWORD(wp) == BN_CLICKED) {
            if (g_moveMode != 1) { g_moveMode = 1; InvalidateRect(g_hCopyRadio, NULL, TRUE); InvalidateRect(g_hMoveRadio, NULL, TRUE); }
        } else if (id == IDC_AI_CHECK && HIWORD(wp) == BN_CLICKED) {
            g_aiMode = !g_aiMode;
            InvalidateRect(g_hAiCheck, NULL, TRUE);
        } else if (id == IDC_API_KEY_EDIT && HIWORD(wp) == EN_CHANGE) {
            GetWindowTextW(g_hApiKeyEdit, g_apiKey, 255);
        } else if (id == IDC_SKIP_BTN && HIWORD(wp) == BN_CLICKED) {
            if (g_running) {
                InterlockedExchange(&g_skipRequested, 1);
            }
        } else if (id == IDC_DRIVE_COMBO && HIWORD(wp) == CBN_SELCHANGE) {
            int idx = (int)SendMessageW(g_hDriveCombo, CB_GETCURSEL, 0, 0);
            if (idx != CB_ERR) {
                wchar_t *root = (wchar_t *)SendMessageW(g_hDriveCombo, CB_GETITEMDATA, idx, 0);
                if (root) SetWindowTextW(g_hPathEdit, root);
            }
        } else if (id == IDC_START_BTN && HIWORD(wp) == BN_CLICKED) {
            if (g_running) break;
            wchar_t path[MAX_PATH];
            GetWindowTextW(g_hPathEdit, path, MAX_PATH);
            size_t len = wcslen(path);
            while (len > 1 && path[len-1] == L'\\') path[--len] = 0;
            if (len == 0 || GetFileAttributesW(path) == INVALID_FILE_ATTRIBUTES) {
                MessageBoxW(hwnd, L"נא לבחור נתיב תקין לסריקה.", L"שגיאה",
                    MB_OK | MB_ICONWARNING | MB_RTLREADING);
                break;
            }

            // Ask where to place the "כל השירים" root folder, instead of
            // automatically nesting it inside the scanned source path.
            wchar_t destPath[MAX_PATH];
            if (!pickFolder(hwnd, L"בחר היכן ליצור את תיקיית \"כל השירים\"", destPath, MAX_PATH)) {
                break; // user cancelled - don't start the scan
            }
            size_t destLen = wcslen(destPath);
            while (destLen > 1 && destPath[destLen-1] == L'\\') destPath[--destLen] = 0;

            SetWindowTextW(g_hLogEdit, L"");
            g_pctCopy = g_pctFolders = g_pctOverall = 0;
            InvalidateRect(g_hBody, NULL, TRUE);
            g_running = 1;
            InterlockedExchange(&g_skipRequested, 0);
            EnableWindow(g_hStartBtn, FALSE);
            EnableWindow(g_hExcludeAddBtn, FALSE);
            EnableWindow(g_hExcludeRemoveBtn, FALSE);
            EnableWindow(g_hSkipBtn, TRUE);
            SetWindowTextW(g_hCurrentLabel, L"מתחיל...");
            InvalidateRect(g_hStartBtn, NULL, TRUE);
            InvalidateRect(g_hExcludeAddBtn, NULL, TRUE);
            InvalidateRect(g_hExcludeRemoveBtn, NULL, TRUE);
            InvalidateRect(g_hSkipBtn, NULL, TRUE);

            WorkerArgs *args = (WorkerArgs *)malloc(sizeof(WorkerArgs));
            wcsncpy(args->sourcePath, path, MAX_PATH - 1);
            wcsncpy(args->destPath, destPath, MAX_PATH - 1);
            args->moveMode = g_moveMode;
            args->aiMode = g_aiMode;
            wcsncpy(args->apiKey, g_apiKey, 255);
            CloseHandle(CreateThread(NULL, 0, workerThread, args, 0, NULL));
        }
        return 0;
    }

    case WM_APP_LOGLINE: {
        wchar_t *line = (wchar_t *)lp;
        appendLog(line);
        free(line);
        return 0;
    }
    case WM_APP_PROGRESS: {
        int value = (int)wp, max = (int)lp;
        if (max <= 0) max = 1;
        g_pctCopy = (int)((__int64)value * 100 / max);
        InvalidateRect(g_hBody, NULL, FALSE);
        return 0;
    }
    case WM_APP_PROGRESS_FOLDERS: {
        int value = (int)wp, max = (int)lp;
        if (max <= 0) max = 1;
        g_pctFolders = (int)((__int64)value * 100 / max);
        InvalidateRect(g_hBody, NULL, FALSE);
        return 0;
    }
    case WM_APP_PROGRESS_OVERALL: {
        int value = (int)wp, max = (int)lp;
        if (max <= 0) max = 1;
        g_pctOverall = (int)((__int64)value * 100 / max);
        InvalidateRect(g_hBody, NULL, FALSE);
        return 0;
    }
    case WM_APP_CURRENT: {
        wchar_t *title = (wchar_t *)lp;
        if (title) {
            wchar_t buf[600];
            swprintf(buf, 600, L"מעתיק כעת: %ls", title);
            SetWindowTextW(g_hCurrentLabel, buf);
            free(title);
        } else {
            SetWindowTextW(g_hCurrentLabel, L"אין פעולה פעילה כרגע");
        }
        return 0;
    }
    case WM_APP_SHOW_REVIEW: {
        RECT mr; GetWindowRect(g_hMain, &mr);
        int w = 480, h = 500;
        int x = mr.left + ((mr.right - mr.left) - w) / 2;
        int y = mr.top + ((mr.bottom - mr.top) - h) / 2;
        EnableWindow(g_hMain, FALSE);
        g_hReviewWnd = CreateWindowExW(WS_EX_RTLREADING | WS_EX_DLGMODALFRAME,
            L"SongOrganizerReviewWnd",
            g_reviewIsArtistMode ? L"אישור זמרים שזוהו" : L"אישור כפילויות שנמצאו",
            WS_CAPTION | WS_SYSMENU | WS_POPUP,
            x, y, w, h, g_hMain, NULL, NULL, NULL);
        ShowWindow(g_hReviewWnd, SW_SHOW);
        SetForegroundWindow(g_hReviewWnd);
        return 0;
    }
    case WM_APP_DONE: {
        g_running = 0;
        // Snap all three rings to full - covers early-exit paths (e.g. no
        // songs found) that never drove a ring to its max themselves.
        g_pctCopy = g_pctFolders = g_pctOverall = 100;
        InvalidateRect(g_hBody, NULL, FALSE);
        EnableWindow(g_hStartBtn, TRUE);
        EnableWindow(g_hExcludeAddBtn, TRUE);
        EnableWindow(g_hExcludeRemoveBtn, TRUE);
        EnableWindow(g_hSkipBtn, FALSE);
        SetWindowTextW(g_hCurrentLabel, L"הריצה הסתיימה");
        InvalidateRect(g_hStartBtn, NULL, TRUE);
        InvalidateRect(g_hExcludeAddBtn, NULL, TRUE);
        InvalidateRect(g_hExcludeRemoveBtn, NULL, TRUE);
        InvalidateRect(g_hSkipBtn, NULL, TRUE);
        return 0;
    }

    case WM_TIMER:
        /* Animation timer is no longer started (see WM_CREATE) - kept as a
           harmless no-op in case anything else ever sets timer id 1. */
        return 0;
    
    case WM_DESTROY:
        if (g_animTimer) KillTimer(hwnd, g_animTimer);
        PostQuitMessage(0);
        return 0;
    }
    return DefWindowProcW(hwnd, msg, wp, lp);
}

/* ============================ g_hBody window proc ============================
 * Hosts every card/control below the header and owns the vertical scrolling:
 * scrollbar range/position, mouse-wheel, and drawing the cards themselves
 * (using g_scrollY, via computeCardRects). All UI logic that used to live in
 * the main WndProc for these controls (button clicks, colors, owner-draw)
 * stays exactly where it was - WM_COMMAND/WM_DRAWITEM/WM_CTLCOLOR* just get
 * forwarded to it unchanged, since g_hBody is now their immediate parent and
 * Windows delivers those messages to whichever window a control's immediate
 * parent is. */
static LRESULT CALLBACK BodyWndProc(HWND hwnd, UINT msg, WPARAM wp, LPARAM lp) {
    switch (msg) {
    case WM_SIZE:
        updateBodyScroll(hwnd, TRUE);
        return 0;

    case WM_VSCROLL: {
        SCROLLINFO si = { sizeof(si) };
        si.fMask = SIF_ALL;
        GetScrollInfo(hwnd, SB_VERT, &si);
        int pos = si.nPos;
        switch (LOWORD(wp)) {
            case SB_LINEUP:        pos -= SCROLL_STEP; break;
            case SB_LINEDOWN:      pos += SCROLL_STEP; break;
            case SB_PAGEUP:        pos -= (int)si.nPage; break;
            case SB_PAGEDOWN:      pos += (int)si.nPage; break;
            case SB_THUMBTRACK:
            case SB_THUMBPOSITION: pos = si.nTrackPos; break;
            case SB_TOP:            pos = si.nMin; break;
            case SB_BOTTOM:         pos = si.nMax; break;
            default: return 0;
        }
        int maxPos = si.nMax - (int)si.nPage + 1;
        if (maxPos < 0) maxPos = 0;
        if (pos < 0) pos = 0;
        if (pos > maxPos) pos = maxPos;
        if (pos != g_scrollY) {
            g_scrollY = pos;
            updateBodyScroll(hwnd, TRUE);
        }
        return 0;
    }

    case WM_MOUSEWHEEL: {
        int wheelDelta = (short)HIWORD(wp); // +120 per notch up, -120 per notch down
        RECT rc; GetClientRect(hwnd, &rc);
        int content = computeContentHeight(hwnd);
        int maxPos = content - (rc.bottom - rc.top);
        if (maxPos < 0) maxPos = 0;
        int newPos = g_scrollY - (wheelDelta / WHEEL_DELTA) * SCROLL_STEP * 3;
        if (newPos < 0) newPos = 0;
        if (newPos > maxPos) newPos = maxPos;
        if (newPos != g_scrollY) {
            g_scrollY = newPos;
            updateBodyScroll(hwnd, TRUE);
        }
        return 0;
    }

    case WM_ERASEBKGND:
        return 1; // same reasoning as the main window - WM_PAINT below always redraws everything itself

    case WM_PAINT: {
        PAINTSTRUCT ps;
        HDC screenDc = BeginPaint(hwnd, &ps);

        RECT rc; GetClientRect(hwnd, &rc);
        int w = rc.right - rc.left;
        int h = rc.bottom - rc.top;
        if (w < 1) w = 1;
        if (h < 1) h = 1;

        HDC dc = CreateCompatibleDC(screenDc);
        HBITMAP bmp = CreateCompatibleBitmap(screenDc, w, h);
        HBITMAP oldBmp = (HBITMAP)SelectObject(dc, bmp);

        FillRect(dc, &rc, g_hBrushBg);

        CardRects c = computeCardRects(hwnd, g_scrollY);
        drawCard(dc, c.source);
        drawCard(dc, c.action);
        drawCard(dc, c.log);

        /* bold section titles, drawn straight onto the card background */
        SetBkMode(dc, TRANSPARENT);
        SetTextColor(dc, g_clrText);
        HFONT oldTitleFont = SelectObject(dc, g_hFontSection);
        RECT tSrc = { c.source.left + MARGIN, c.source.top + 10, c.source.right - MARGIN, c.source.top + 32 };
        DrawTextW(dc, g_cardTitleSettings, -1, &tSrc, DT_RIGHT | DT_VCENTER | DT_SINGLELINE);
        RECT tAct = { c.action.left + MARGIN, c.action.top + 10, c.action.right - MARGIN, c.action.top + 32 };
        DrawTextW(dc, g_cardTitleAction, -1, &tAct, DT_CENTER | DT_VCENTER | DT_SINGLELINE);
        RECT tLog = { c.log.left + MARGIN, c.log.top + 10, c.log.right - MARGIN, c.log.top + 32 };
        DrawTextW(dc, g_cardTitleLog, -1, &tLog, DT_RIGHT | DT_VCENTER | DT_SINGLELINE);
        SelectObject(dc, oldTitleFont);

        /* three donut progress rings in the middle column */
        drawProgressRing(dc, g_ringRect[0], g_pctCopy,    RGB(0x2F, 0x7B, 0xE0), L"התחלה");
        drawProgressRing(dc, g_ringRect[1], g_pctFolders, RGB(0x1E, 0x2A, 0x44), L"יצירת תיקיות ומיון");
        drawProgressRing(dc, g_ringRect[2], g_pctOverall, RGB(0xF4, 0x7C, 0x20), L"התקדמות כללית");

        BitBlt(screenDc, 0, 0, w, h, dc, 0, 0, SRCCOPY);

        SelectObject(dc, oldBmp);
        DeleteObject(bmp);
        DeleteDC(dc);

        EndPaint(hwnd, &ps);
        return 0;
    }

    /* These four all target whichever window is the control's immediate
       parent - that's g_hBody now, so hand them straight to the main
       window's WndProc, where all the actual handling already lives
       (button clicks, edit/listbox/static colors, owner-drawn buttons). */
    case WM_COMMAND:
    case WM_DRAWITEM:
    case WM_CTLCOLORSTATIC:
    case WM_CTLCOLOREDIT:
    case WM_CTLCOLORLISTBOX:
        return WndProc(g_hMain, msg, wp, lp);
    }
    return DefWindowProcW(hwnd, msg, wp, lp);
}

/* --- candidate-pair review window: shown once (after the whole scan/pair
 * phase) listing every pair-folder name that didn't match a known artist,
 * with a checkbox per row (checked = "זמר", unchecked = "טעות תוכנה"). The
 * worker thread is blocked on g_reviewDoneEvent while this is on screen. */
static void reviewFinalize(HWND hwnd) {
    for (int i = 0; i < candidatePairCount; i++) {
        candidatePairs[i].approved = ListView_GetCheckState(g_hReviewList, i) ? 1 : 0;
    }
    EnableWindow(g_hMain, TRUE);
    SetForegroundWindow(g_hMain);
    DestroyWindow(hwnd);
    g_hReviewWnd = NULL;
    SetEvent(g_reviewDoneEvent);
}

static LRESULT CALLBACK ReviewWndProc(HWND hwnd, UINT msg, WPARAM wp, LPARAM lp) {
    switch (msg) {
    case WM_CREATE: {
        const wchar_t *labelText = g_reviewIsArtistMode
            ? L"אלו הזמרים שזוהו בשירים שנסרקו (לפי רשימת הזמרים הידועה). הסר סימון ✓ ממי שלא רלוונטי - שיריו יעברו למיון לפי א-ב יחד עם שירים שלא זוהה להם זמר כלל. לחץ 'אישור והמשך' רק אחרי שסיימת לסמן."
            : L"אלה צירופים/שמות שחוזרים בין שירים. סמן ✓ ליד כפילות שעבורה תרצה ליצור תיקייה בשם הכפילות; כפילות שלא תסומן לא תקבל תיקייה והשירים שלה יעברו לתיקיית 'אחר'.";
        g_hReviewLabel = CreateWindowExW(WS_EX_RTLREADING, L"STATIC",
            labelText,
            WS_CHILD | WS_VISIBLE | SS_RIGHT, 16, 12, 448, 44, hwnd, NULL, NULL, NULL);
        SendMessageW(g_hReviewLabel, WM_SETFONT, (WPARAM)g_hFont, TRUE);

        g_hReviewList = CreateWindowExW(WS_EX_RTLREADING | WS_EX_CLIENTEDGE, WC_LISTVIEWW, NULL,
            WS_CHILD | WS_VISIBLE | LVS_REPORT | LVS_SINGLESEL,
            16, 60, 448, 380, hwnd, NULL, NULL, NULL);
        ListView_SetExtendedListViewStyle(g_hReviewList, LVS_EX_CHECKBOXES | LVS_EX_FULLROWSELECT | LVS_EX_GRIDLINES);
        LVCOLUMNW col = {0};
        col.mask = LVCF_TEXT | LVCF_WIDTH;
        col.cx = 320; col.pszText = g_reviewIsArtistMode ? L"שם הזמר שזוהה" : L"שם התיקייה המועמדת";
        ListView_InsertColumn(g_hReviewList, 0, &col);
        col.cx = 100; col.pszText = L"שירים";
        ListView_InsertColumn(g_hReviewList, 1, &col);

        for (int i = 0; i < candidatePairCount; i++) {
            LVITEMW item = {0};
            item.mask = LVIF_TEXT;
            item.iItem = i;
            item.pszText = candidatePairs[i].name;
            ListView_InsertItem(g_hReviewList, &item);
            wchar_t cnt[16]; swprintf(cnt, 16, L"%d", candidatePairs[i].songCount);
            ListView_SetItemText(g_hReviewList, i, 1, cnt);
            // Artist-list matches are already certain, so every row starts
            // checked; the "unsure shared-word pair" flow keeps starting
            // unchecked (user opts IN there instead of opting OUT).
            if (g_reviewIsArtistMode) ListView_SetCheckState(g_hReviewList, i, TRUE);
        }

        g_hReviewOkBtn = CreateWindowExW(0, L"BUTTON", L"אישור והמשך",
            WS_CHILD | WS_VISIBLE, 16, 452, 448, 34, hwnd, (HMENU)1, NULL, NULL);
        SendMessageW(g_hReviewOkBtn, WM_SETFONT, (WPARAM)g_hFontBold, TRUE);
        return 0;
    }
    case WM_COMMAND:
        if (LOWORD(wp) == 1 && HIWORD(wp) == BN_CLICKED) reviewFinalize(hwnd);
        return 0;
    case WM_CLOSE:
        reviewFinalize(hwnd);
        return 0;
    case WM_CTLCOLORSTATIC: {
        HDC dc = (HDC)wp;
        SetTextColor(dc, g_clrText);
        SetBkMode(dc, TRANSPARENT);
        return (LRESULT)GetStockObject(NULL_BRUSH);
    }
    }
    return DefWindowProcW(hwnd, msg, wp, lp);
}

int WINAPI wWinMain(HINSTANCE hInst, HINSTANCE hPrev, LPWSTR cmdLine, int nCmdShow) {
    (void)hPrev; (void)cmdLine;

    songs = (Song *)malloc(sizeof(Song) * MAX_SONGS);
    pairs = (PairEntry *)malloc(sizeof(PairEntry) * MAX_UNIQUE_PAIRS);
    aiArtists = (AiArtistEntry *)malloc(sizeof(AiArtistEntry) * MAX_SONGS);
    nodePool = (PairNode *)malloc(sizeof(PairNode) * MAX_SONGS * MAX_WORDS_PER_SONG);
    songPairIndex = malloc(sizeof(int) * MAX_SONGS * MAX_WORDS_PER_SONG);
    assignedPair = (int *)malloc(sizeof(int) * MAX_SONGS);

    INITCOMMONCONTROLSEX icc = { sizeof(icc), ICC_PROGRESS_CLASS | ICC_STANDARD_CLASSES | ICC_LISTVIEW_CLASSES };
    InitCommonControlsEx(&icc);
    CoInitialize(NULL);
    g_reviewDoneEvent = CreateEventW(NULL, TRUE, FALSE, NULL);

    const wchar_t *clsName = L"SongOrganizerGuiWnd";
    WNDCLASSEXW wc = {0};
    wc.cbSize = sizeof(wc);
    wc.style = 0; /* no CS_HREDRAW/CS_VREDRAW: those force an extra erase+paint
                     pass on every resize, which isn't needed since WM_SIZE
                     below already re-lays-out and repaints everything itself */
    wc.lpfnWndProc = WndProc;
    wc.hInstance = hInst;
    wc.hCursor = LoadCursorW(NULL, IDC_ARROW);
    wc.hIcon = LoadIconW(NULL, IDI_APPLICATION);
    wc.lpszClassName = clsName;
    wc.hbrBackground = NULL;
    RegisterClassExW(&wc);

    /* g_hBody's class - must be registered before g_hMain is created, since
       g_hMain's own WM_CREATE creates g_hBody as one of its first steps. */
    const wchar_t *bodyClsName = L"SongOrganizerBodyWnd";
    WNDCLASSEXW wcBody = {0};
    wcBody.cbSize = sizeof(wcBody);
    wcBody.style = 0;
    wcBody.lpfnWndProc = BodyWndProc;
    wcBody.hInstance = hInst;
    wcBody.hCursor = LoadCursorW(NULL, IDC_ARROW);
    wcBody.lpszClassName = bodyClsName;
    wcBody.hbrBackground = NULL;
    RegisterClassExW(&wcBody);

    const wchar_t *reviewClsName = L"SongOrganizerReviewWnd";
    WNDCLASSEXW wcReview = {0};
    wcReview.cbSize = sizeof(wcReview);
    wcReview.style = 0;
    wcReview.lpfnWndProc = ReviewWndProc;
    wcReview.hInstance = hInst;
    wcReview.hCursor = LoadCursorW(NULL, IDC_ARROW);
    wcReview.lpszClassName = reviewClsName;
    wcReview.hbrBackground = CreateSolidBrush(g_clrBg);
    RegisterClassExW(&wcReview);

    g_hMain = CreateWindowExW(WS_EX_RTLREADING | WS_EX_COMPOSITED,
        clsName, L"מארגן שירים - Modern",
        WS_OVERLAPPEDWINDOW,
        CW_USEDEFAULT, CW_USEDEFAULT, 720, 900,  /* Larger, more spacious */
        NULL, NULL, hInst, NULL);

    ShowWindow(g_hMain, nCmdShow);
    UpdateWindow(g_hMain);

    MSG msg;
    while (GetMessageW(&msg, NULL, 0, 0)) {
        TranslateMessage(&msg);
        DispatchMessageW(&msg);
    }
    return 0;
}