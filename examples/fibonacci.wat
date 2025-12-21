(module
  (type (;0;) (func (param i32) (result i32)))
  (export "fibonacci" (func 0))
  (func (;0;) (type 0) (param i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32)
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
    local.set 4
    block ;; label = @1
      local.get 4
      br_if 0 (;@1;)
      local.get 0
      i32.const 1
      i32.eq
      local.set 3
      block ;; label = @2
        local.get 3
        br_if 0 (;@2;)
        local.get 0
        i32.const 1
        i32.sub
        local.set 5
        local.get 0
        i32.const 2
        i32.sub
        local.set 6
        local.get 5
        call 0
        local.set 1
        local.get 6
        call 0
        local.set 2
        local.get 1
        local.get 2
        i32.add
        local.set 7
        local.get 7
        local.set 8
        local.get 8
        i32.const 0
        i32.ge_s
        i32.eqz
        if ;; label = @3
          unreachable
        end
        local.get 8
        return
      end
      i32.const 0
      local.set 8
      local.get 8
      i32.const 0
      i32.ge_s
      i32.eqz
      if ;; label = @2
        unreachable
      end
      local.get 8
      return
    end
    i32.const 1
    local.set 8
    local.get 8
    i32.const 0
    i32.ge_s
    i32.eqz
    if ;; label = @1
      unreachable
    end
    local.get 8
    return
  )
)
