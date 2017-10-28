# xalloc

[<img src="https://docs.rs/xalloc/badge.svg" alt="docs.rs">](https://docs.rs/tokenlock/)

Dynamic suballocators for external memory (e.g., Vulkan device memory).

## Provided Algorithms

|               Name              | Time Complexity | Space Complexity |
| ------------------------------- | --------------- | ---------------- |
| TLSF (Two-Level Segregated Fit) | `O(1)`          | `O(N)`           |
| Free space bitmap               | `O(size)`       | `O(size)`        |

(`size`: heap size measured by the number of allocation units, `N`: number of allocations)

## Examples

```rust
let mut tlsf = xalloc::SysTlsf::new(8u32);

// Allocate regions
let (region1, offset1) = tlsf.alloc(4).unwrap();
let (region2, offset2) = tlsf.alloc(4).unwrap();
println!("allocated #1: {:?}", (&region1, offset1));
println!("allocated #2: {:?}", (&region2, offset2));

// Deallocate a region
tlsf.dealloc(region1).unwrap();

// Now we can allocate again
tlsf.alloc(2).unwrap();
tlsf.alloc(2).unwrap();
```

## Feature Flags

- `nightly` — Enables optimizations which currently require a Nightly Rust
  compiler.


License: MIT
