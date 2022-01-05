# Security Reports

Rust strives to be a completely memory-safe language, and libraries written in
it should also. `bitvec` has a strict requirement that it *must* have correct,
safe, behavior first and foremost; performance and convenience are subordinate
goals.

If you find a memory-safety violation in `bitvec`, please file an issue here
describing what occurred, the platform on which it occurred, and either a code
sample or a backtrace that I can use to find the error. In the past, I have been
able to find error sources from a small sample and a description of intent and
the failure.

I will work with you on all correctness errors to find the fault and write a fix
in as rapid a time-frame as I am able. Once you have verified that I have
resolved the fault, I will publish the fix as a new patch version on *at least*
the minor series that observed the fault, and any others that I deem worthwhile.

Depending on the severity of the fault, I *may* yank affected versions from the
Rust registry <https://crates.io>. As of this writing, the `0.x.y` versions are
all unsupported, but will remain published unless serious vulnerabilities are
discovered. I do not plan to provide security updates to the version-0 series
anymore.

`bitvec` is a pointer-encoding library. It is at risk for vulnerabilities in its
encoding and decoding of memory addresses, and its use of the memory allocator.
It *should* be unaffected by other classes of vulnerability.

## What Is and Is Not an Error

Any incorrect behavior found when operating on a `bitvec` data structure that
has not been modified or tampered with by the user is a fault in `bitvec`, and
should be reported. However, `bitvec` does not, and cannot, proäctively defend
against adversarial modification of the objects it gives to users. Incorrect
modification of objects later passed in to `bitvec` *will* crash your system,
and this is *not* a bug in `bitvec`.

Incorrect behavior includes, but is not limited to, race conditions, memory
access violations, lost writes, spurious writes, and allocator mismanagement. In
general, any deviation from the behavior of the Rust standard library types that
`bitvec` replaces is a fault in `bitvec`.
