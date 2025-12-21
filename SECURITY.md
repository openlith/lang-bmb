# Security Policy

## Supported Versions

| Version | Supported          |
| ------- | ------------------ |
| 0.2.x   | :white_check_mark: |
| 0.1.x   | :x:                |

## Reporting a Vulnerability

If you discover a security vulnerability in BMB, please report it responsibly.

### How to Report

1. **Do NOT** open a public issue for security vulnerabilities
2. Email the security report to the maintainers (see repository for contact)
3. Include:
   - Description of the vulnerability
   - Steps to reproduce
   - Potential impact
   - Suggested fix (if any)

### What to Expect

- Acknowledgment within 48 hours
- Status update within 7 days
- We will work with you to understand and resolve the issue
- Credit will be given in the security advisory (if desired)

## Security Considerations

### Compiler Security

BMB is a compiler that generates WebAssembly. Security considerations include:

1. **Input Validation**: The parser validates all input against the BMB grammar
2. **Type Safety**: The type checker prevents type confusion vulnerabilities
3. **Contract Verification**: Runtime contract checks catch logic errors
4. **WASM Sandbox**: Generated code runs in WebAssembly's sandbox

### Known Limitations

- **No Static Contract Verification**: Currently, contracts are verified at runtime only (Silver level). Static verification (Gold level) is planned.
- **Integer Overflow**: BMB does not automatically check for integer overflow. Use contracts to specify valid ranges.
- **Division by Zero**: Use `@pre divisor != 0` contracts to prevent division by zero.

### Best Practices for BMB Code

1. **Always write contracts**: Define preconditions and postconditions
2. **Check division**: Add `@pre b != 0` before any division by `b`
3. **Validate ranges**: Use preconditions to prevent overflow
4. **Use the linter**: `bmbc lint` catches common security issues

### Example: Safe Division

```bmb
@node safe_divide
@params a:i32 b:i32
@returns i32
@pre b != 0                    # Prevent division by zero
@post true

  div %r a b
  ret %r
```

### Example: Range Validation

```bmb
@node factorial
@params n:i32
@returns i32
@pre n >= 0 && n <= 12         # Prevent overflow for i32
@post ret >= 1

  # Implementation...
```

## Security Updates

Security updates will be released as patch versions. Subscribe to releases to stay informed.
