#!/bin/python3

import math
import os
import random
import time


def generate_grid(required_words: list[str], forbidden_words: list[str]) -> list[str]:
    dirs = [(dr, dc) for dr in (-1, 0, 1) for dc in (-1, 0, 1) if (dr, dc) != (0, 0)]
    az = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

    def clean(words):
        seen = set()
        out = []
        for word in words:
            word = (word or "").strip().upper()
            if word and word not in seen:
                seen.add(word)
                out.append(word)
        return out

    required_all = clean(required_words)
    forbidden = clean(forbidden_words)
    if not required_all:
        return ["A"]

    def covered_by(word, other):
        return word in other or word[::-1] in other

    required = []
    for word in sorted(required_all, key=lambda w: (-len(w), w)):
        if not any(covered_by(word, kept) for kept in required):
            required.append(word)

    seed = "\n".join(required_all) + "\0" + "\n".join(forbidden)
    rng = random.Random(seed)

    single_forbidden = {word for word in forbidden if len(word) == 1}
    filler_alphabet = "".join(ch for ch in az if ch not in single_forbidden) or az
    safe_fillers = [ch for ch in filler_alphabet if ch not in set("".join(forbidden))]
    req_letters = "".join(required)
    fill_letters = "".join(ch for ch in sorted(set(req_letters)) if ch not in single_forbidden)
    if not fill_letters:
        fill_letters = filler_alphabet

    longest = max(map(len, required_all))
    min_n = max(longest, math.ceil(math.sqrt(len(set(req_letters)))))
    deadline = time.perf_counter() + (0.22 if len(required) <= 180 else 0.35)

    def cells_for(n, row, col, dr, dc, length):
        return tuple(((row + dr * i) % n) * n + (col + dc * i) % n for i in range(length))

    def row_strings(grid, n):
        return ["".join(grid[r * n:(r + 1) * n]) for r in range(n)]

    def contains_word(grid, n, word):
        use_dirs = ((0, 1),) if len(word) == 1 else dirs
        for row in range(n):
            for col in range(n):
                for dr, dc in use_dirs:
                    for i, ch in enumerate(word):
                        if grid[((row + dr * i) % n) * n + (col + dc * i) % n] != ch:
                            break
                    else:
                        return True
        return False

    def first_forbidden_hits(grid, n, limit=1):
        for word in forbidden:
            use_dirs = ((0, 1),) if len(word) == 1 else dirs
            for row in range(n):
                for col in range(n):
                    for dr, dc in use_dirs:
                        cells = cells_for(n, row, col, dr, dc, len(word))
                        if all(grid[cell] == word[i] for i, cell in enumerate(cells)):
                            limit -= 1
                            if limit == 0:
                                return True
        return False

    def build_placements(n):
        placements = {}
        for word in required:
            use_dirs = ((0, 1),) if len(word) == 1 else dirs
            lines = []
            seen = set()
            limit = 320

            def add(row, col, dr, dc):
                cells = cells_for(n, row, col, dr, dc, len(word))
                if len(set(cells)) != len(word) or cells in seen:
                    return
                seen.add(cells)
                lines.append(cells)

            for row in range(min(n, 10)):
                add(row, 0, 0, 1)
                add(0, row, 1, 0)
                if len(word) > 1:
                    add(row, row, 1, 1)
                    add(row, row, 1, -1)

            tries = 0
            while len(lines) < limit and tries < limit * 3:
                tries += 1
                dr, dc = rng.choice(use_dirs)
                add(rng.randrange(n), rng.randrange(n), dr, dc)
            placements[word] = lines
        return placements

    def build_forbidden_index(n):
        by_cell = [[] for _ in range(n * n)]
        for word in sorted(forbidden, key=len)[:160]:
            if len(word) > n:
                continue
            use_dirs = ((0, 1),) if len(word) == 1 else dirs
            seen = set()
            for row in range(n):
                for col in range(n):
                    for dr, dc in use_dirs:
                        cells = cells_for(n, row, col, dr, dc, len(word))
                        if cells in seen:
                            continue
                        seen.add(cells)
                        entry = (word, cells)
                        for cell in set(cells):
                            by_cell[cell].append(entry)
        return by_cell

    def makes_forbidden(grid, placed, bad_by_cell):
        checked = set()
        for cell in placed:
            for entry in bad_by_cell[cell]:
                if entry in checked:
                    continue
                checked.add(entry)
                bad_word, cells = entry
                for i, check_cell in enumerate(cells):
                    ch = placed.get(check_cell, grid[check_cell])
                    if ch is None or ch != bad_word[i]:
                        break
                else:
                    return True
        return False

    def choose_candidate(grid, counts, word, lines, bad_by_cell, attempt):
        best = []
        if len(lines) > 220:
            step = max(1, len(lines) // 220)
            lines = lines[(attempt * 13) % step::step]

        for cells in lines:
            overlap = 0
            pressure = 0
            ok = True
            placed = {}
            for i, cell in enumerate(cells):
                current = grid[cell]
                if current is not None and current != word[i]:
                    ok = False
                    break
                placed[cell] = word[i]
                if current == word[i]:
                    overlap += 1
                    pressure += counts[cell]
            if ok and forbidden and makes_forbidden(grid, placed, bad_by_cell):
                ok = False
            if ok:
                score = overlap * 100 + pressure * 7 - (len(word) - overlap) * 4 + rng.random()
                best.append((score, cells))

        if not best:
            return None
        best.sort(reverse=True, key=lambda item: item[0])
        return rng.choice(best[: min(len(best), 1 + attempt // 7)])[1]

    def finish_grid(grid, counts, n):
        protected = [count > 0 for count in counts]
        base_fill = safe_fillers if forbidden and safe_fillers else list(fill_letters)

        for fill_attempt in range(8 if forbidden else 1):
            candidate = grid[:]
            for i, ch in enumerate(candidate):
                if ch is None:
                    candidate[i] = base_fill[0] if fill_attempt == 0 else rng.choice(base_fill)

            if not forbidden:
                return candidate

            for _ in range(90):
                if not first_forbidden_hits(candidate, n, 1):
                    return candidate

                repaired = False
                for word in sorted(forbidden, key=len):
                    if repaired:
                        break
                    use_dirs = ((0, 1),) if len(word) == 1 else dirs
                    for row in range(n):
                        if repaired:
                            break
                        for col in range(n):
                            if repaired:
                                break
                            for dr, dc in use_dirs:
                                cells = cells_for(n, row, col, dr, dc, len(word))
                                if all(candidate[cell] == word[i] for i, cell in enumerate(cells)):
                                    choices = [cell for cell in cells if not protected[cell]]
                                    if not choices:
                                        return None
                                    cell = rng.choice(choices)
                                    letters = [ch for ch in base_fill if ch != candidate[cell]]
                                    candidate[cell] = rng.choice(letters or base_fill)
                                    repaired = True
                                    break
        return None

    def greedy_pack(n, placements, bad_by_cell, attempt):
        grid = [None] * (n * n)
        counts = [0] * (n * n)
        ordered = required[:]
        ordered.sort(key=lambda w: (-len(w), sum(req_letters.count(ch) for ch in set(w))))
        if attempt:
            rng.shuffle(ordered)

        for word in ordered:
            cells = choose_candidate(grid, counts, word, placements[word], bad_by_cell, attempt)
            if cells is None:
                return None
            for i, cell in enumerate(cells):
                if counts[cell] == 0:
                    grid[cell] = word[i]
                counts[cell] += 1
        return finish_grid(grid, counts, n)

    max_extra = max(5, min(12, len(required) // 5 + 5))
    for n in range(min_n, min_n + max_extra + 1):
        if time.perf_counter() >= deadline:
            break
        placements = build_placements(n)
        if any(not placements[word] for word in required):
            continue
        bad_by_cell = build_forbidden_index(n) if forbidden else [[] for _ in range(n * n)]

        local_deadline = min(deadline, time.perf_counter() + 0.02 + 0.001 * len(required))
        attempt = 0
        while time.perf_counter() < local_deadline:
            packed = greedy_pack(n, placements, bad_by_cell, attempt)
            if packed is not None and (not forbidden or not first_forbidden_hits(packed, n, 1)):
                return row_strings(packed, n)
            attempt += 1

    def separated_fallback():
        if forbidden and safe_fillers:
            fill = safe_fillers[0]
            n = max(longest + 1, 2 * len(required) + 1, min_n)
            for extra in range(8):
                size = n + extra
                grid = [[fill for _ in range(size)] for _ in range(size)]
                for i, word in enumerate(required):
                    row = (2 * i) % size
                    for col, ch in enumerate(word[:size]):
                        grid[row][col] = ch
                flat = [ch for row in grid for ch in row]
                if not first_forbidden_hits(flat, size, 1):
                    return row_strings(flat, size)
            return ["".join(row) for row in grid]

        n = max(longest, len(required), min_n)
        fill = filler_alphabet[0]
        grid = [[fill for _ in range(n)] for _ in range(n)]
        for row, word in enumerate(required[:n]):
            for col, ch in enumerate(word[:n]):
                grid[row][col] = ch
        return ["".join(row) for row in grid]

    return separated_fallback()


if __name__ == "__main__":
    fptr = open(os.environ["OUTPUT_PATH"], "w")

    required_words_count = int(input().strip())
    required_words = [input() for _ in range(required_words_count)]

    forbidden_words_count = int(input().strip())
    forbidden_words = [input() for _ in range(forbidden_words_count)]

    grid = generate_grid(required_words, forbidden_words)

    fptr.write("\n".join([" ".join(x) for x in grid]))
    fptr.write("\n")

    fptr.close()
