use parity_scale_codec::{Compact, CompactLen, Decode, Encode, Error, Input};

fn reference_encode(x: u32) -> Vec<u8> {
	match x {
		0..=63 => vec![(x as u8) << 2],
		64..=16_383 => (((x as u16) << 2) | 1).to_le_bytes().to_vec(),
		16_384..=1_073_741_823 => ((x << 2) | 2).to_le_bytes().to_vec(),
		_ => {
			let mut encoded = vec![3];
			encoded.extend_from_slice(&x.to_le_bytes());
			encoded
		},
	}
}

fn reference_len(x: u32) -> usize {
	match x {
		0..=63 => 1,
		64..=16_383 => 2,
		16_384..=1_073_741_823 => 4,
		_ => 5,
	}
}

struct GuardedInput<'a> {
	bytes: &'a [u8],
	pos: usize,
	failed: bool,
}

impl Input for GuardedInput<'_> {
	fn remaining_len(&mut self) -> Result<Option<usize>, Error> {
		Ok(Some(self.bytes.len() - self.pos))
	}

	fn read(&mut self, into: &mut [u8]) -> Result<(), Error> {
		assert!(!self.failed, "decoder read after an input failure");
		let end = self.pos.saturating_add(into.len());
		if end > self.bytes.len() {
			self.failed = true;
			return Err("guarded input exhausted".into());
		}
		into.copy_from_slice(&self.bytes[self.pos..end]);
		self.pos = end;
		Ok(())
	}
}

fn values() -> Vec<u32> {
	let mut values: Vec<_> = (0..=65_535).collect();
	for boundary in [0u32, 63, 64, 16_383, 16_384, 1_073_741_823, 1_073_741_824, u32::MAX] {
		for delta in 0..=8 {
			values.extend(boundary.checked_sub(delta));
			values.extend(boundary.checked_add(delta));
		}
	}
	let mut x = 0x6d2b_79f5u32;
	for _ in 0..100_000 {
		x = x.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
		values.push(x);
	}
	values
}

#[test]
fn public_compact_u32_matches_verified_model() {
	for x in values() {
		let encoded = Compact(x).encode();
		assert_eq!(encoded, reference_encode(x), "encoding mismatch for {x}");
		assert_eq!(encoded.len(), reference_len(x), "length mismatch for {x}");
		assert_eq!(Compact::compact_len(&x), reference_len(x), "CompactLen mismatch for {x}");
		let mut input = encoded.as_slice();
		assert_eq!(Compact::<u32>::decode(&mut input).unwrap().0, x);
		assert!(input.is_empty(), "decode left bytes for {x}");
	}
}

#[test]
fn public_compact_u32_truncation_stays_within_input() {
	for x in [0u32, 63, 64, 16_383, 16_384, 1_073_741_823, 1_073_741_824, u32::MAX] {
		let encoded = Compact(x).encode();
		for cut in 0..encoded.len() {
			let mut input = GuardedInput { bytes: &encoded[..cut], pos: 0, failed: false };
			assert!(
				Compact::<u32>::decode(&mut input).is_err(),
				"truncation decoded for {x} at {cut}"
			);
			assert!(input.pos <= cut, "decode over-read for {x} at {cut}");
		}
	}
}
