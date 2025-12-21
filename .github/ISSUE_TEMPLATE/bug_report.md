---
name: Bug Report
about: Report a bug in BMB
title: '[BUG] '
labels: bug
assignees: ''
---

## Description

A clear and concise description of the bug.

## BMB Version

```
bmbc --version
```

Output:

## Environment

- OS: [e.g., Windows 11, Ubuntu 22.04, macOS 14]
- Rust version: [e.g., 1.75.0]

## Reproduction

### Minimal BMB Code

```bmb
@node example
@params x:i32
@returns i32
@pre true
@post true

  # Your code here
  ret x
```

### Command Used

```bash
bmbc compile example.bmb
# or
bmbc run example.bmb -- args
```

### Expected Behavior

What you expected to happen.

### Actual Behavior

What actually happened.

### Error Output

```
Paste full error output here
```

## Additional Context

Add any other context about the problem here.

## Checklist

- [ ] I searched existing issues
- [ ] I included a minimal reproduction
- [ ] I included the full error output
