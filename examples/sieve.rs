/*! Sieve of Eratosthenes

The `bit_vec` crate had this as an example, so I do too, I guess.

Run with

```sh
$ cargo run --release --example sieve -- [max] [count]
```

where max is an optional maximum number below which all primes will be found,
and count is an optional number whose square will be used to display the bottom
primes.

For example,

```sh
$ cargo run --release --example sieve -- 10000000 25
```

will find all primes less than ten million, and print the primes below 625 in a
square 25x25.
!*/

//  Impl notes: If this executable starts segfaulting, `BitPtr::len` might be
//  the culprit. Replace the bare + and - in that function with .saturating_ops
//  and see if that solves it.
//
//  Heisenbugs are weird.

#[cfg(feature = "alloc")]
extern crate bitvec;

#[cfg(feature = "alloc")]
use bitvec::prelude::{
	BigEndian,
	bitvec,
};

#[cfg(feature = "alloc")]
use std::{
	cmp,
	env,
};

#[cfg(feature = "alloc")]
fn main() {
	let max: usize = env::args()
		.nth(1)
		.unwrap_or_else(|| "1000000".into())
		.parse()
		.unwrap_or(1_000_000);

	let primes = {
		let mut bv = bitvec![BigEndian, u64; 1; max];

		//  0 and 1 are not primes
		bv.set(0, false);
		bv.set(1, false);

		for n in 2 ..= ((max as f64).sqrt() as usize) {
			//  Adjust the frequency of log statements vaguely logarithmically.
			if n <  20_000 && n %  1_000 == 0
			|| n <  50_000 && n %  5_000 == 0
			|| n < 100_000 && n % 10_000 == 0 {
				println!("Calculating {}…", n);
			}
			//  If n is prime, mark all multiples as non-prime
			if bv[n] {
				if n < 100 {
					println!("Calculating {}…", n);
				}
				'inner:
				for i in n .. {
					let j = n * i;
					if j >= max {
						break 'inner;
					}
					bv.set(j, false);
				}
			}
		}
		println!("Calculation complete!");

		bv
	};

	if primes.not_any() {
		println!("There are no primes smaller than {}", max);
		std::process::exit(0);
	}

	//  Count primes and non-primes.
	let (mut one, mut zero) = (0u64, 0u64);
	for n in primes.iter() {
		if *n {
			one += 1;
		}
		else {
			zero += 1;
		}
	}
	println!("Counting complete!");

	let dim: usize = env::args()
		.nth(2)
		.unwrap_or_else(|| "10".into())
		.parse()
		.unwrap_or(10);

	let len = primes.len();
	let limit = cmp::min(dim * dim, len);
	//  Find the widest number that will be printed, and get its width.
	let cell_width = primes[.. limit]
		.iter()
		.copied()
		//  search from the back
		.rev()
		.enumerate()
		//  stop at the first prime
		.find(|(_, bit)| *bit)
		//  ceil(log10) is the number of digits to print
		.map(|(idx, _)| ((limit - 1 - idx) as f64).log(10.0).ceil() as usize)
		.expect("Failed to find a prime.");

	println!("There are {} primes and {} non-primes below {}", one, zero, max);
	println!("The primes smaller than {} are:", limit);
	'outer:
	for i in 0 .. dim {
		let h = i * dim;
		if h >= limit {
			break;
		}
		println!();
		for j in 0 .. dim {
			let k = h + j;
			if k >= limit {
				break 'outer;
			}
			if primes[k] {
				print!("{:>1$} ", k, cell_width);
			}
			else {
				print!("{:^1$} ", "-", cell_width);
			}
		}
	}
	println!();
}

#[cfg(not(any(feature = "alloc", feature = "std")))]
fn main() {
	println!("This example only runs when an allocator is present");
}
