# Introduction

Programmers have sought to model memory as a one-dimensional stream of bits for
as long as hardware manufacturers have sought to chunk it into wider and wider
words. `bitvec` is far from the first library to provide this model, and it will
likely not be the last. It is, however, the best (at least in my opinion).

`bitvec` was built out of my experience and frustration with performing I/O
buffer manipulation using C, C++, and Ruby. My work required programs capable of
dynamically selecting a region of a bitstream, a task to which C-style bitfield
declarations were unsuited, and it required those programs to be fast, which is
not an adjective one commonly associates with Ruby engines.

Furthermore, my work involved message schemata that were permitted to select a
bit ordering at the packet and field level. This is *not* a behavior that any
existing bitstream library or language feature provides. These experiences
informed my goals and design choices from the very beginning.

`bitvec` matches, and exceeds, the functionality of every other bitstream
implementation I have found. It is also the only Rust crate that is a drop-in
replacement for standard library types, and is able to do so without taking a
performance loss. Thanks to excellent compiler engineering by the Rust and LLVM
teams, it often produces code that exactly matches, and sometimes surpasses,
the bit-shift/mask assembly logic you would write yourself.

## Goals of This Book

I intend for this book to serve as an explanation of `bitvec`’s design choices
and philosophy. It is not a detailed exploration of the crate APIs – [docs.rs]
exists – but instead seeks to communicate how to think about `bitvec` so that
you will know how to use the APIs offered.

The best way that I know how to communicate this information is as a dialogue
between me, the author, and you, the user. Since this is a book, not a
conversation, I actively encourage you to get in contact with me with any
questions through the channels listed in the repository’s [CONTRIBUTING]
document, and throughout the book I will periodically remind you that if a
section is unclear, it is an error on my part, and I would appreciate an issue
or other contact so that I can improve it.

[CONTRIBUTING]: https://github.com/myrrlyn/bitvec/blob/HEAD/CONTRIBUTING.md "project contribution guide"
[docs.rs]: https://docs.rs/bitvec "bitvec API documentation"
