/* Temporary build fallback: the original project depends on an external artist_array.c.
 * This file keeps the interface intact so the Windows build can be validated.
 * Replace this file with the project's full artist list for automatic singer matching.
 */
#define ARTIST_COUNT 1
static const wchar_t *ARTIST_LIST[ARTIST_COUNT] = { L"" };
