import sys

def find_matching_paren(s, start):
    assert s[start] == '('
    depth = 0
    for i in range(start, len(s)):
        if s[i] == '(':
            depth += 1
        elif s[i] == ')':
            depth -= 1
            if depth == 0:
                return i
    raise ValueError("Unbalanced parentheses")

def rewrite_once(s):
    i = 0
    out = []
    changed = False

    while i < len(s):
        if s.startswith("op(", i):
            a_start = i + 2  # points at '('
            a_end = find_matching_paren(s, a_start)
            if a_end + 1 < len(s) and s[a_end + 1] == '(':
                b_start = a_end + 1
                b_end = find_matching_paren(s, b_start)

                A = s[a_start + 1 : a_end]
                B = s[b_start + 1 : b_end]

                out.append(f"op({A}, *, {B})")
                i = b_end + 1
                changed = True
                continue

        out.append(s[i])
        i += 1

    return "".join(out), changed

def rewrite_all(s):
    while True:
        s, changed = rewrite_once(s)
        if not changed:
            return s

if __name__ == "__main__":
    text = sys.stdin.read()
    print(rewrite_all(text), end="")
