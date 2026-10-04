// SongOrganizer - Windows GUI version
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
    if (SUCCEEDED(store->lpVtbl->GetValue(store, &key, &pv)))
        propVariantToText(&pv, out, outCap);
    PropVariantClear(&pv);
}

static void readMusicMetadata(const wchar_t *path, Song *s) {
    s->metaTitle[0] = s->artist[0] = s->album[0] = s->albumArtist[0] = s->composer[0] = 0;
    s->conductor[0] = s->contentGroup[0] = s->publisher[0] = s->subtitle[0] = 0;
    s->writer[0] = s->producer[0] = 0;
    IPropertyStore *store = NULL;
    HRESULT hr = SHGetPropertyStoreFromParsingName(path, NULL, GPS_BESTEFFORT, IID_PPV_ARGS(&store));
    if (SUCCEEDED(hr) && store) {
        readStringProperty(store, PKEY_Title, s->metaTitle, MAX_PATH);
        readStringProperty(store, PKEY_Music_Artist, s->artist, MAX_PATH);
        readStringProperty(store, PKEY_Music_AlbumTitle, s->album, MAX_PATH);
        readStringProperty(store, PKEY_Music_AlbumArtist, s->albumArtist, MAX_PATH);
        readStringProperty(store, PKEY_Music_Composer, s->composer, MAX_PATH);
        readStringProperty(store, PKEY_Music_Conductor, s->conductor, MAX_PATH);
        readStringProperty(store, PKEY_Music_ContentGroupDescription, s->contentGroup, MAX_PATH);
        readStringProperty(store, PKEY_Media_Publisher, s->publisher, MAX_PATH);
        readStringProperty(store, PKEY_Media_SubTitle, s->subtitle, MAX_PATH);
        readStringProperty(store, PKEY_Media_Writer, s->writer, MAX_PATH);
        readStringProperty(store, PKEY_Media_Producer, s->producer, MAX_PATH);
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
    if (hConnect) {