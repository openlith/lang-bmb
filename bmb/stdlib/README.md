# BMB Standard Library

This directory contains standard library modules for BMB programs.

## Available Modules

### io.bmb - File I/O (v0.13+)

Provides file system access through host-imported functions.

**Import Name**: `"bmb" "io_*"` (WASM imports)

**Functions**:
- `io_open(path, path_len, mode) -> fd`
- `io_read(fd, buf, len) -> bytes_read`
- `io_write(fd, buf, len) -> bytes_written`
- `io_close(fd) -> status`
- `io_size(fd) -> size`
- `io_seek(fd, offset, whence) -> position`
- `io_exists(path, path_len) -> status`
- `io_flush(fd) -> status`

**Usage in BMB**:
```bmb
@node read_file
@params fd:i32 buf:*u8 len:i32
@returns i32

  xcall %result io_read %fd %buf %len
  ret %result
```

## Host Implementation

WASM hosts must provide these functions as imports. See `src/host/io.rs` 
for a reference implementation.

### Minimal Host (Rust + wasmtime)

```rust
use wasmtime::*;

fn create_io_imports(store: &mut Store<()>, linker: &mut Linker<()>) {
    linker.func_wrap("bmb", "io_open", |path: i32, len: i32, mode: i32| -> i32 {
        // Implement file open
        -1 // Not implemented
    }).unwrap();
    
    linker.func_wrap("bmb", "io_read", |fd: i32, buf: i32, len: i32| -> i32 {
        // Implement file read
        -1
    }).unwrap();
    
    // ... etc
}
```

## File Descriptor Convention

| FD | Description |
|----|-------------|
| 0  | stdin       |
| 1  | stdout      |
| 2  | stderr      |
| 3+ | User files  |

## Error Codes

| Code | Meaning |
|------|---------|
| -1   | General error |
| -2   | File not found |
| -3   | Permission denied |
| -4   | Out of memory |
| -5   | Invalid argument |
| -6   | Too many open files |
