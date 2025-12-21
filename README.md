# BMB - Bare-Metal-Banter

> **"Omission is guessing, and guessing is error."**

Bare-metal programming is grueling for humans, but for AI, it's just banter with the machine.

---

## Philosophy

| Principle | Description |
|-----------|-------------|
| **Omission is Guessing** | What is omitted must be guessed by the writer |
| **Explicit is Mandatory** | Explicitness is not preferred, it's enforced |
| **Compile-time over Runtime** | Errors must be caught before execution |
| **Contracts are Code** | Contracts are verified code, not comments |
| **Writer Diligence over Human Convenience** | Assumes tireless writer (AI), abandons human convenience |

---

## Decision Criteria

```
Allows omission? → Make it mandatory
Discovered at runtime? → Move to compile-time
For human convenience? → Remove or redesign
In separate docs? → Integrate into language spec (contracts)
```

---

## Code = Documentation

```bmb
@node divide
@params a:f64 b:f64
@returns f64
@pre b != 0           # Doc: "b must not be zero"
@post ret * b == a    # Doc: "guarantees correct division"

  div %r a b
  ret %r
```

No separate documentation needed. Contracts are the specification.

---

## Goals

| Metric | Current | BMB |
|--------|---------|-----|
| First-gen success rate | 60% | 90%+ |
| Debug iterations | 3-5 | 0-1 |

---

## Documentation

- [SPECIFICATION.md](docs/SPECIFICATION.md)

---

MIT License
