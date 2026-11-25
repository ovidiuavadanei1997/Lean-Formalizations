"""Small, dependency-free source checks; the Lean kernel checks the mathematics."""
import hashlib
import re


def comments(text):
    """Return nested Lean comment spans, ignoring comment markers in strings."""
    spans = []
    i = 0
    while i < len(text):
        if text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == '\\':
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            else:
                raise ValueError('unterminated string')
        elif text.startswith('--', i):
            j = text.find('\n', i)
            j = len(text) if j < 0 else j
            spans.append((i, j))
            i = j
        elif text.startswith('/-', i):
            start, depth = i, 1
            i += 2
            while i < len(text) and depth:
                if text.startswith('/-', i):
                    depth += 1
                    i += 2
                elif text.startswith('-/', i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ValueError('unterminated comment')
            spans.append((start, i))
        else:
            i += 1
    return spans


def code(text):
    chars = list(text)
    for a, b in comments(text):
        chars[a:b] = ['\n' if c == '\n' else ' ' for c in text[a:b]]
    return ''.join(chars)


def tokens(text):
    # Preserve whole string literals and identifier boundaries, including primes.
    return re.findall(r'"(?:\\.|[^"\\])*"|[\w\u2080-\u209f]+[\w\u2080-\u209f\']*|[^\s]', code(text))


def code_hash(text):
    return hashlib.sha256('\0'.join(tokens(text)).encode()).hexdigest()


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
