# Compact u32 verification boundary

- production path
  - public `Compact<u32>` through `Encode`, `Decode`, and `CompactLen`
  - implementation in `src/compact.rs`
- proof
  - `compact_u32.rs` repeats the production branch bounds, tag construction, little-endian byte layout, decode reconstruction, and atomic slice-input consumption model
  - proves round trip, length agreement, range/tag partition, five-byte form, and bounded truncation consumption for every `u32`
- correspondence
  - `tests/compact_u32_correspondence.rs` compares the verified formulas with the real public API over dense low values, all boundaries, and deterministic full-width samples
  - guarded `Input` checks truncated production decodes fail without consuming beyond available bytes
- exclusions
  - derive macros, custom `CompactAs`, collections, memory tracking, `u64`, `u128`, chain-wide consensus, and `ArrayVec` memory safety
- claim limit
  - the Verus proof establishes the explicit model
  - ordinary Rust tests and the pre-edit search establish bounded correspondence to production; they are not a formal verification of Rust compiler output or every `Input` implementation
