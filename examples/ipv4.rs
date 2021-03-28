/*! This example demonstrates building an IPv4 packet header using `BitField`.

The example program will run through the construction of the header at the speed
of your terminal's buffer. The program can be made interactive, pausing after
each modification so that the user can manually step to the next, by running it
with the argument "pause": `cargo run --example ipv4 -- pause`
!*/

use std::{
	collections::BTreeSet,
	fmt::{
		self,
		Display,
		Formatter,
	},
	io,
	ops::Range,
};

use bitvec::prelude::*;
use wyz::fmt::FmtForward;

type Ipv4Header = BitArray<Msb0, [u8; 20]>;

/// Build up an IPv4 packet
fn build() -> Ipv4Header {
	let mut pkt: Ipv4Header = BitArray::zeroed();
	render("Starting with a blank packet", &pkt, 0 .. 0);

	//  Set IPv4
	pkt[.. 4].store(4u8);
	render("Set IP version to 4", &pkt, 0 .. 4);
	//  Set an IHL of 5 words
	pkt[4 .. 8].store(5u8);
	render(
		"Set header length to 5 32-bit words (20 bytes)",
		&pkt,
		4 .. 8,
	);
	//  Set the DSCP to "low drop, class 3" per Wikipedia
	pkt[8 .. 14].store(0b011010u8);
	render("Set DSCP number", &pkt, 8 .. 14);
	//  Set the ECN flag to "ECT(0)", per RFC 3168
	pkt[14 .. 16].store(0b10u8);
	render("Set ECN flag", &pkt, 14 .. 16);

	//  Set a total size of 20 bytes. The storage API will convert to
	//  big-endian.
	pkt[16 .. 32].store_be(20u16);
	render(
		"Set total packet length to 20 bytes (no payload)",
		&pkt,
		16 .. 32,
	);

	//  Set the identification fingerprint
	pkt[32 .. 48].store_be(0xACABu16);
	render("Set an identifying fingerprint", &pkt, 32 .. 48);

	//  Set the flags
	*pkt.get_mut(48).unwrap() = true;
	*pkt.get_mut(49).unwrap() = false;
	*pkt.get_mut(50).unwrap() = true;
	render("Set some flags", &pkt, 48 .. 51);

	//  Set the fragment offset to be 758, the age of the library in days
	pkt[51 .. 64].store_be(758u16);
	render("Set the fragment offset to 758", &pkt, 51 .. 64);

	//  Set the TTL to 27 (my age in years)
	pkt.as_mut_raw_slice()[8] = 27;
	render("Set the TTL", &pkt, 64 .. 72);
	//  Set the protocol number to 17 (UDP)
	pkt.as_mut_raw_slice()[9] = 17;
	render("Set the protocol number", &pkt, 72 .. 80);

	//  Fill in the IP addresses using ordinary byte accesses
	for (slot, byte) in pkt.as_mut_raw_slice()[12 .. 20]
		.iter_mut()
		.zip(&[127, 0, 0, 1, 192, 168, 1, 254])
	{
		*slot = *byte;
	}
	render("Fill the source IP addresses", &pkt, 96 .. 160);

	//  Last, set the checksum
	let csum = ipv4_csum(&pkt[..]);
	pkt[80 .. 96].store_be::<u16>(csum);
	render("Set the checksum", &pkt, 80 .. 96);

	pkt
}

fn parse(header: BitArray<Msb0, [u8; 20]>) {
	assert_eq!(ipv4_csum(&header[..]), 0);

	//  Check that the version field is `4`, by `load`ing it and by direct
	//  inspection
	assert_eq!(header[.. 4].load::<u8>(), 4);
	assert_eq!(header.as_raw_slice()[0] & 0xF0, 0x40);

	let ihl = header[4 .. 8].load::<u8>() as usize;
	assert!((5 .. 16).contains(&ihl));
	assert!(!header[49], "Unexpected fragmentation");
	assert!(header[50], "Unexpected fragmentation");

	eprintln!("Final packet: [");
	for byte in &header.into_inner() {
		eprintln!("    {:08b}", *byte);
	}
	eprintln!("]");
}

fn main() {
	eprintln!("Press <Enter> to move through the steps of the example");
	parse(build());
}

fn ipv4_csum(header: &BitSlice<Msb0, u8>) -> u16 {
	if !(160 .. 288).contains(&header.len()) {
		panic!("IPv4 headers must be between 160 and 288 bits");
	}
	let mut accum = 0u32;
	for pair in header.chunks(16) {
		accum += pair.load_be::<u16>() as u32;
	}
	while accum > 0xFFFFu32 {
		let high = accum & !0xFFFFu32;
		accum += high >> 16;
		accum -= high;
	}
	!(accum as u16)
}

fn render(title: &'static str, packet: &Ipv4Header, range: Range<usize>) {
	eprintln!("{}: {:#}", title, AnnotatedArray::new(packet, range));
	if std::env::args().last().unwrap() == "pause" {
		let _ = io::stdin().read_line(&mut String::new()).unwrap();
	}
}

struct AnnotatedArray<'a> {
	packet: &'a Ipv4Header,
	range: Range<usize>,
}

impl<'a> AnnotatedArray<'a> {
	fn new(packet: &'a Ipv4Header, range: Range<usize>) -> Self {
		Self { packet, range }
	}
}

impl<'a> Display for AnnotatedArray<'a> {
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		let mut out = fmt.debug_list();
		let marked_bits = self.range.clone().collect::<BTreeSet<_>>();
		let mut word_string = String::with_capacity(41);
		let mut mark_string = String::with_capacity(41);
		for (idx, word) in self.packet.as_bitslice().chunks(32).enumerate() {
			let start_bit = idx * 32;
			let bits = start_bit .. start_bit + 32;
			for (bit, idx) in word.iter().by_val().zip(bits) {
				word_string.push_str(if bit { "1" } else { "0" });
				mark_string.push_str(if marked_bits.contains(&idx) {
					"^"
				}
				else {
					" "
				});
				if idx % 8 == 7 && idx % 32 != 31 {
					word_string.push_str(" ");
					mark_string.push_str(" ");
				}
			}
			out.entry(&(&word_string).fmt_display());
			if !mark_string.trim().is_empty() {
				out.entry(&(&mark_string).fmt_display());
			}
			word_string.clear();
			mark_string.clear();
		}
		out.finish()
	}
}
