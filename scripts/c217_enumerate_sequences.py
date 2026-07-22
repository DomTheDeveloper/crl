#!/usr/bin/env python3
from itertools import combinations_with_replacement


def hh_step_desc(s):
    if not s:
        return ()
    d, *rest = s
    return tuple(sorted((max(0, x - 1) if i < d else x for i, x in enumerate(rest)), reverse=True))


def residue(s):
    s = tuple(sorted(s, reverse=True))
    while s and s[0] != 0:
        s = hh_step_desc(s)
    return len(s)


def graphical(s):
    s = list(sorted(s, reverse=True))
    while s:
        if s[0] == 0:
            return True
        d = s.pop(0)
        if d > len(s):
            return False
        for i in range(d):
            s[i] -= 1
            if s[i] < 0:
                return False
        s.sort(reverse=True)
    return True


def chvatal_path(desc):
    d = tuple(reversed(desc))
    n = len(d)
    for i in range(1, (n + 1) // 2 + 1):
        if 2 * i < n + 1 and d[i - 1] < i and d[n - i] < n - i:
            return False
    return True


def rows(low_delta_only):
    ans = []
    for n in range(2, 15):
        for asc in combinations_with_replacement(range(1, min(6, n - 1) + 1), n):
            desc = tuple(reversed(asc))
            if sum(desc) % 2:
                continue
            if low_delta_only and min(desc) >= 4:
                continue
            if graphical(desc) and residue(desc) == 2 and not chvatal_path(desc):
                ans.append((n, desc))
    return ans


def emit(title, data):
    print(f'## {title}')
    print()
    print(f'Total: **{len(data)}**')
    print()
    for i, (n, s) in enumerate(data, 1):
        print(f'{i:03d}. n={n}: `{list(s)}`')
    print()


print('# WOWII 217 exact degree-sequence diagnostics')
print()
emit('All residue-two sequences failing the path Chvatal criterion', rows(False))
emit('Low-minimum-degree remainder (delta <= 3)', rows(True))
