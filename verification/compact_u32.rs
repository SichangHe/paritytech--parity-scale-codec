use vstd::prelude::*;

verus! {

pub struct Encoded {
	pub b0: u8,
	pub b1: u8,
	pub b2: u8,
	pub b3: u8,
	pub b4: u8,
	pub len: nat,
}

pub open spec fn compact_len(x: u32) -> nat {
	if x <= 63 { 1 } else if x <= 16_383 { 2 } else if x <= 1_073_741_823 { 4 } else { 5 }
}

pub open spec fn mode(x: u32) -> u8 {
	if x <= 63 { 0 } else if x <= 16_383 { 1 } else if x <= 1_073_741_823 { 2 } else { 3 }
}

pub open spec fn encode(x: u32) -> Encoded {
	if x <= 63 {
		Encoded { b0: (x as u8) << 2, b1: 0, b2: 0, b3: 0, b4: 0, len: 1 }
	} else if x <= 16_383 {
		let y = ((x as u16) << 2) | 1;
		Encoded {
			b0: y as u8,
			b1: (y >> 8) as u8,
			b2: 0,
			b3: 0,
			b4: 0,
			len: 2,
		}
	} else if x <= 1_073_741_823 {
		let y = (x << 2) | 2;
		Encoded {
			b0: y as u8,
			b1: (y >> 8) as u8,
			b2: (y >> 16) as u8,
			b3: (y >> 24) as u8,
			b4: 0,
			len: 4,
		}
	} else {
		Encoded {
			b0: 3,
			b1: x as u8,
			b2: (x >> 8) as u8,
			b3: (x >> 16) as u8,
			b4: (x >> 24) as u8,
			len: 5,
		}
	}
}

pub open spec fn decode(e: Encoded) -> u32 {
	if e.b0 & 3 == 0 {
		(e.b0 >> 2) as u32
	} else if e.b0 & 3 == 1 {
		(((e.b0 as u16) | ((e.b1 as u16) << 8)) >> 2) as u32
	} else if e.b0 & 3 == 2 {
		((e.b0 as u32)
			| ((e.b1 as u32) << 8)
			| ((e.b2 as u32) << 16)
			| ((e.b3 as u32) << 24)) >> 2
	} else {
		(e.b1 as u32)
			| ((e.b2 as u32) << 8)
			| ((e.b3 as u32) << 16)
			| ((e.b4 as u32) << 24)
	}
}

pub open spec fn can_decode(e: Encoded, available: nat) -> bool {
	available >= e.len
}

pub open spec fn consumed_on_attempt(e: Encoded, available: nat) -> nat {
	if available == 0 { 0 } else if can_decode(e, available) { e.len } else { 1 }
}

proof fn mode0_bits(x: u32) by (bit_vector)
	requires x <= 63,
	ensures
		((((x as u8) << 2) >> 2) as u32) == x,
		((x as u8) << 2) & 3 == 0,
{
}

proof fn mode1_bits(x: u32) by (bit_vector)
	requires 64 <= x <= 16_383,
	ensures
		(((((x as u16) << 2) | 1) as u8) & 3) == 1,
		((
			((((x as u16) << 2) | 1) as u8) as u16
				| (((((((x as u16) << 2) | 1) >> 8) as u8) as u16) << 8)
		) >> 2) as u32 == x,
{
}

proof fn mode2_bits(x: u32) by (bit_vector)
	requires 16_384 <= x <= 1_073_741_823,
	ensures
		((((x << 2) | 2) as u8) & 3) == 2,
		(((x << 2) | 2) as u8) as u32
			| ((((((x << 2) | 2) >> 8) as u8) as u32) << 8)
			| ((((((x << 2) | 2) >> 16) as u8) as u32) << 16)
			| ((((((x << 2) | 2) >> 24) as u8) as u32) << 24) == (x << 2) | 2,
		((x << 2) | 2) >> 2 == x,
{
}

proof fn mode3_bits(x: u32) by (bit_vector)
	ensures
		((x as u8) as u32)
			| ((((x >> 8) as u8) as u32) << 8)
			| ((((x >> 16) as u8) as u32) << 16)
			| ((((x >> 24) as u8) as u32) << 24) == x,
{
}

proof fn roundtrip(x: u32)
	ensures decode(encode(x)) == x,
{
	if x <= 63 {
		mode0_bits(x);
		assert(decode(encode(x)) == x);
	} else if x <= 16_383 {
		mode1_bits(x);
		assert(decode(encode(x)) == x);
	} else if x <= 1_073_741_823 {
		mode2_bits(x);
		assert(decode(encode(x)) == x);
	} else {
		mode3_bits(x);
		assert(3u8 & 3 == 3) by (bit_vector);
		assert(decode(encode(x)) == x);
	}
}

proof fn length_and_tag(x: u32)
	ensures
		encode(x).len == compact_len(x),
		encode(x).b0 & 3 == mode(x),
{
	if x <= 63 {
		mode0_bits(x);
	} else if x <= 16_383 {
		mode1_bits(x);
	} else if x <= 1_073_741_823 {
		mode2_bits(x);
	} else {
		assert(3u8 & 3 == 3) by (bit_vector);
	}
}

proof fn range_partition(x: u32)
	ensures
		(mode(x) == 0) == (x <= 63),
		(mode(x) == 1) == (64 <= x && x <= 16_383),
		(mode(x) == 2) == (16_384 <= x && x <= 1_073_741_823),
		(mode(x) == 3) == (1_073_741_824 <= x),
{
}

proof fn five_byte_form(x: u32)
	requires 1_073_741_824 <= x,
	ensures
		encode(x).len == 5,
		encode(x).b0 == 3,
		decode(encode(x)) == x,
{
	roundtrip(x);
}

proof fn truncated_decode_does_not_overread(x: u32, available: nat)
	requires available < compact_len(x),
	ensures
		!can_decode(encode(x), available),
		consumed_on_attempt(encode(x), available) <= available,
{
}

}

fn main() {}
