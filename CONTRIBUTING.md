# Contributing Guide

Contributions, requests, questions, and general contacts are absolutely welcome!

## Contact Information

In order of likelihood that I will actionably receive your contact, my
information is:

- Email: [self@myrrlyn.dev](mailto:self@myrrlyn.dev)
- GitHub: [@myrrlyn](https://github.com/myrrlyn)
- Twitter: [@bitvec_rs](https://twitter.com/bitvec_rs)
- Twitter: [@myrrlyn](https://twitter.com/myrrlyn)
- Mastodon: [@myrrlyn@cybre.space](https://cybre.space/myrrlyn)
- Reddit: [/u/myrrlyn](https://reddit.com/u/myrrlyn)
- Discord: `@myrrlyn#0611`. I am present in the Rust Programming Language and in
  the Rust Programming Language Community servers. If you are in either, you can
  ping me in them, or DM me.

I am not active on any IRC channels at this time. I have a very consistent
username scheme and so anywhere you see my name, it’s *probably* me and I’ll
*probably* respond to it.

## Preconditions

Be able to make a Rust project compile. I will happily help you learn how to do
this, but this particular crate is probably not something you want to explore as
a beginner.

Be comfortable using `U+0009 CHARACTER TABULATION` as your indentation setting.

That’s about it for prerequisites! This crate intends to power the lowest level
of memory manipulation while also offering a convenient, powerful, and idiomatic
high-level API, so I encourage and welcome inputs on any aspect of this crate’s
construction. I know that I personally am much more capable at the low end than
the high, and so the user-facing API may not be as strong as it should be.

## Contributing

If you have a patch you think is worth inspecting right away, opening a pull
request without prelude is fine, although I would certainly appreciate an
accompanying explanation of what the patch does and why.

If you have questions, bugs, suggestions, or other contributions of any kind
that do not immediately touch the codebase, you can reach me informally to talk
about them or open an issue.

I will do my best to respond to all contacts in a timely manner.

## Environment

This project is formatted with the following command:

```sh
cargo +nightly fmt -- --config-path rustfmt-nightly.toml
```

A smaller `rustfmt.toml` is provided which is capable of being executed by the
pinned stable `rustfmt`; however, as `rustfmt` is an unstable tool, the nightly
formatter is used to handle more complex configuration.

Please ensure that you run this formatter before sending in a PR, in order to
avoid excessive noise.
