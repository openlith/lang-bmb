(module
  (type (;0;) (func (param i32) (result i32)))
  (export "factorial" (func 0))
  (func (;0;) (type 0) (param i32) (result i32)
    (local i32 i32 i32 i32)
    local.get 0
    i32.const 0
    i32.ge_s
    i32.eqz
    if ;; label = @1
      unreachable
    end
    local.get 0
    i32.const 0
    i32.eq
    local.set 1
    local.get 1
    br_if 0
    local.get 0
    i32.const 1
    i32.sub
    local.set 2
    local.get 2
    call 0
    local.set 3
    local.get 0
    local.get 3
    i32.mul
    local.set 3
    local.get 3
    local.set 4
    local.get 4
    i32.const 1
    i32.ge_s
    i32.eqz
    if ;; label = @1
      unreachable
    end
    local.get 4
    return
    i32.const 1
    local.set 4
    local.get 4
    i32.const 1
    i32.ge_s
    i32.eqz
    if ;; label = @1
      unreachable
    end
    local.get 4
    return
  )
)
