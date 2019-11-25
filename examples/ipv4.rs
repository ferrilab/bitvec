/*! This example demonstrates building an IPv4 packet header using `BitField`.

There are still some flaws and missing functionality in the `BitField` trait,
which provides capabilities for addressing regions of memory other than the
fundamental types as storage/value slots, that hamper usability. However, for
bitfields that *are* supported, the trait provides conveniences over bare
shift/masks.
!*/

extern crate bitvec;

use bitvec::prelude::*;

fn build() -> [u8; 20] {
	let mut raw_bytes = [0u8; 20];
	let pkt = raw_bytes.bits_mut::<BigEndian>();

	//  Set IPv4
	pkt[.. 4].store(4u8);
	//  Set an IHL of 5 words
	pkt[4 .. 8].store(5u8);
	//  Blank the DSCP and ECN fields
	pkt[8 .. 14].store(0u8);
	pkt[14 .. 16].store(0u8);

	//  Set a total size of 20 bytes. This must be encoded as big-endian before
	//  storage, as the storage API does not currently provide this.
	pkt[16 .. 32].store(20u16.to_be());

	//  Set the identification fingerprint
	pkt[32 .. 48].store(0xC001u16.to_be());

	//  Set the flags
	*pkt.at(48) = false;
	*pkt.at(49) = true;
	*pkt.at(50) = false;

	/* And the fragment offset. Until `BitField` stabilizes byte-endian APIs,
	this will remain unpleasant. `0u16` can be stored in `[51 .. 64]` without
	trouble, as can `!0u16`, but no other bit pattern can be currently stored
	correctly in IPv4’s expectation of big-endian byte ordering using the
	`BitField` API on a little-endian machine. This will be addressed in a
	future release.
	*/
	pkt[51 .. 56].store(0u8);
	pkt[56 .. 64].store(0u8);

	//  There are no more bitfields in the IPv4 header, so the rest can be
	//  filled normally
	raw_bytes[12 .. 16].clone_from_slice(&[127, 0, 0, 1]);
	raw_bytes[16 .. 20].clone_from_slice(&[192, 168, 1, 254]);

	//  Last, set the checksum
	let csum = ipv4_csum(&raw_bytes[..]);
	raw_bytes[10] = (csum >> 8) as u8;
	raw_bytes[11] = (csum & 0x00FF) as u8;

	raw_bytes
}

fn parse(header: [u8; 20]) {
	assert_eq!(ipv4_csum(&header[..]), 0);
	let pkt = header.bits::<BigEndian>();

	//  Check that the version field is `4`, by `load`ing it and by direct
	//  inspection
	assert_eq!(pkt[.. 4].load::<u8>().unwrap(), 4);
	assert_eq!(header[0] & 0xF0, 0x40);

	let ihl = pkt[4 .. 8].load::<u8>().unwrap() as usize;
	assert!((5 .. 16).contains(&ihl));
	assert!(pkt[49], "Unexpected fragmentation");
	assert!(!pkt[50], "Unexpected fragmentation");
}

fn main() {
	parse(build());
}

fn ipv4_csum(header: &[u8]) -> u16 {
	if !(20 .. 36).contains(&header.len()) {
		panic!("IPv4 headers must be between 20 and 36 bytes");
	}
	let mut accum = 0u32;
	for pair in header.chunks(2) {
		accum += u16::from_be_bytes([pair[0], pair[1]]) as u32;
	}
	while accum > 0xFFFFu32 {
		let high = accum & !0xFFFFu32;
		accum += high >> 16;
		accum -= high;
	}
	!(accum as u16)
}
