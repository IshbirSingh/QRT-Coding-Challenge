import math
import os
import random
import time


def generate_grid(required_words: list[str], forbidden_words: list[str]) -> list[str]:
    dirs = [(dr, dc) for dr in (-1, 0, 1) for dc in (-1, 0, 1) if (dr, dc) != (0, 0)]
    az = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

    def clean(words):
        return list(dict.fromkeys(w.strip().upper() for w in words if w and w.strip()))

    required = clean(required_words)
    raw_forbidden = clean(forbidden_words)
    forbidden = [
        w for w in raw_forbidden
        if not any(w in r or w in r[::-1] for r in required)
    ]
    rng = random.Random("\n".join(required) + "\0" + "\n".join(forbidden))

    req_alphabet = "".join(sorted({ch for word in required for ch in word}))
    single_forbidden = {w for w in forbidden if len(w) == 1}
    fallback_alphabet = "".join(ch for ch in az if ch not in single_forbidden) or az
    alphabet = req_alphabet or fallback_alphabet
    if not required:
        return [fallback_alphabet[0]]

    total_letters = sum(map(len, required))
    longest = max(map(len, required), default=1)
    distinct = len(set("".join(required)))
    start_n = max(
        1,
        longest,
        int(math.sqrt(total_letters / 1.7)) if total_letters else 1,
        math.ceil(math.sqrt(distinct)) if distinct else 1,
    )
    safe_fillers = [ch for ch in fallback_alphabet if ch not in set("".join(forbidden))]

    def simple_construct():
        filler = (safe_fillers or [fallback_alphabet[0]])[0]
        if not forbidden:
            n = max(start_n, len(required))
            grid = [[filler] * n for _ in range(n)]
            for row, word in enumerate(required):
                grid[row][:len(word)] = word
            return ["".join(row) for row in grid]

        if safe_fillers:
            n = max(start_n, longest + 1, 2 * len(required))
            grid = [[filler] * n for _ in range(n)]
            for i, word in enumerate(required):
                grid[2 * i][:len(word)] = word
            return ["".join(row) for row in grid]
        return None

    def build_lines(n: int):
        words = required + [word for word in forbidden if len(word) <= n]
        line_words, line_cells, by_cell = [], [], [[] for _ in range(n * n)]
        by_required = [[] for _ in required]
        seen = set()
        for word_index, word in enumerate(words):
            use_dirs = ((0, 1),) if len(word) == 1 else dirs
            for row in range(n):
                for col in range(n):
                    for dr, dc in use_dirs:
                        cells = tuple(((row + dr * i) % n) * n + (col + dc * i) % n for i in range(len(word)))
                        key = (word_index, cells)
                        if len(set(cells)) == len(word) and key not in seen:
                            seen.add(key)
                            line_index = len(line_words)
                            line_words.append(word_index)
                            line_cells.append(cells)
                            for cell in cells:
                                by_cell[cell].append(line_index)
                            if word_index < len(required):
                                by_required[word_index].append(line_index)
        return words, line_words, line_cells, by_cell, by_required

    def make_state(n: int):
        letters = alphabet if rng.random() < 0.9 else fallback_alphabet
        return [rng.choice(letters) for _ in range(n * n)]

    def matches(grid, word, cells):
        return all(grid[cell] == word[i] for i, cell in enumerate(cells))

    def initial_state(grid, words, line_words, line_cells):
        line_hits = [0] * len(line_words)
        word_hits = [0] * len(words)
        bad = set()
        for i, word_index in enumerate(line_words):
            hit = int(matches(grid, words[word_index], line_cells[i]))
            line_hits[i] = hit
            word_hits[word_index] += hit
            if hit and word_index >= len(required):
                bad.add(i)
        missing = {i for i in range(len(required)) if word_hits[i] == 0}
        return line_hits, word_hits, missing, bad

    def update_cell(grid, words, line_words, line_cells, by_cell, line_hits, word_hits, missing, bad, cell, letter):
        old_letter = grid[cell]
        if old_letter == letter:
            return 0

        touched = by_cell[cell]
        affected_required = {line_words[i] for i in touched if line_words[i] < len(required)}
        before = sum(i in missing for i in affected_required) + sum(i in bad for i in touched)
        grid[cell] = letter

        for line_index in touched:
            word_index = line_words[line_index]
            new_hit = int(matches(grid, words[word_index], line_cells[line_index]))
            old_hit = line_hits[line_index]
            if new_hit == old_hit:
                continue
            line_hits[line_index] = new_hit
            word_hits[word_index] += new_hit - old_hit
            if word_index >= len(required):
                (bad.add if new_hit else bad.discard)(line_index)

        for word_index in affected_required:
            (missing.add if word_hits[word_index] == 0 else missing.discard)(word_index)
        after = sum(i in missing for i in affected_required) + sum(i in bad for i in touched)
        return after - before

    def choose_move(n, grid, words, line_words, line_cells, by_required, missing, bad):
        if missing and rng.random() < 0.72:
            word_index = rng.choice(tuple(missing))
            word = words[word_index]
            ids = by_required[word_index]
            sample_size = min(64, len(ids))
            sample = [ids[rng.randrange(len(ids))] for _ in range(sample_size)]
            best = max(
                sample,
                key=lambda i: sum(grid[cell] == word[j] for j, cell in enumerate(line_cells[i])),
            )
            misses = [j for j, cell in enumerate(line_cells[best]) if grid[cell] != word[j]]
            pos = rng.choice(misses or range(len(word)))
            return line_cells[best][pos], word[pos]

        if bad and rng.random() < 0.55:
            line_index = rng.choice(tuple(bad))
            word = words[line_words[line_index]]
            pos = rng.randrange(len(word))
            cell = line_cells[line_index][pos]
            pool = alphabet if rng.random() < 0.7 else fallback_alphabet
            choices = [ch for ch in pool if ch != word[pos]] or fallback_alphabet
            return cell, rng.choice(choices)

        pool = alphabet if rng.random() < 0.86 else fallback_alphabet
        return rng.randrange(n * n), rng.choice(pool)

    def anneal(n: int, deadline: float):
        words, line_words, line_cells, by_cell, by_required = build_lines(n)
        if any(not lines for lines in by_required):
            return None

        while time.perf_counter() < deadline:
            grid = make_state(n)
            line_hits, word_hits, missing, bad = initial_state(grid, words, line_words, line_cells)
            cost = len(missing) + len(bad)
            local_start = time.perf_counter()
            local_deadline = min(deadline, local_start + 0.25)

            while time.perf_counter() < local_deadline:
                if cost == 0:
                    return ["".join(grid[r * n:(r + 1) * n]) for r in range(n)]
                progress = (time.perf_counter() - local_start) / max(1e-9, local_deadline - local_start)
                temperature = 1.25 * (1.0 - progress) + 0.04
                cell, letter = choose_move(n, grid, words, line_words, line_cells, by_required, missing, bad)
                old_letter = grid[cell]
                delta = update_cell(
                    grid, words, line_words, line_cells, by_cell,
                    line_hits, word_hits, missing, bad, cell, letter
                )
                if delta > 0 and rng.random() >= math.exp(-delta / temperature):
                    update_cell(
                        grid, words, line_words, line_cells, by_cell,
                        line_hits, word_hits, missing, bad, cell, old_letter
                    )
                else:
                    cost += delta
            if cost == 0:
                return ["".join(grid[r * n:(r + 1) * n]) for r in range(n)]
        return None

    if forbidden and safe_fillers:
        result = anneal(start_n, time.perf_counter() + 0.04)
        return result if result is not None else simple_construct()

    n = start_n
    attempts = 2 if not forbidden else 3
    budget = 0.08 if not forbidden else 0.10
    for _ in range(attempts):
        result = anneal(n, time.perf_counter() + budget)
        if result is not None:
            return result
        n += 1
    

if __name__ == '__main__':
    fptr = open(os.environ['OUTPUT_PATH'], 'w')

    required_words_count = int(input().strip())

    required_words = []

    for _ in range(required_words_count):
        required_words_item = input()
        required_words.append(required_words_item)

    forbidden_words_count = int(input().strip())

    forbidden_words = []

    for _ in range(forbidden_words_count):
        forbidden_words_item = input()
        forbidden_words.append(forbidden_words_item)

    grid = generate_grid(required_words, forbidden_words)

    fptr.write('\n'.join([' '.join(x) for x in grid]))
    fptr.write('\n')

    fptr.close()