# Contributing Guide

Contributions, feature requests, usage questions, and general contacts of any
kind are *absolutely* welcome!

Note that this is a hobbyist project, and I work on it in my free time. I can
only give a best-effort promise of availability or responsiveness, but please do
reach out to me with anything you need.

## Contact Information

In roughly descending order of likelihood that I will receive your contact and
reply to it, my information is:

- Email: [self@myrrlyn.dev](mailto:self@myrrlyn.dev)
- GitHub: [@myrrlyn](https://github.com/myrrlyn)
- Project Twitter: [@bitvecto_rs](https://twitter.com/bitvec_rs)
- Personal Twitter: [@myrrlyn](https://twitter.com/myrrlyn)
- Discord: `@myrrlyn#0611`. I am present in the Rust Programming Language and
  Rust Programming Language Community servers. If you are in either, you can
  @-mention me in them, or DM me.

- Reddit: [/u/myrrlyn](https://reddit.com/u/myrrlyn)
- Mastodon: [@myrrlyn@cybre.space](https://cybre.space/myrrlyn)

I am not active on any IRC channels at this time. I have a very consistent
username and so anywhere you see it, it’s *probably* me and I’ll *probably*
respond to it.

## Preconditions

You should be able to drive Cargo. I will happily help you learn how to do this,
but this particular project is probably not something you want to explore as a
beginner.

Be comfortable using `U+0009 CHARACTER TABULATION` as your indentation setting.
If your editor understands `.editorconfig`, or if you use rustfmt, this will
happen automatically.

That’s about it for prerequisites! This project intends to power the lowest
level of memory manipulation while also offering a convenient, powerful, and
idiomatic high-level API, so I welcome *and actively encourage* inputs on any
aspects of this project’s construction, or especially its documentation. I know
that I personally am intimately familiar with its operation and use, and may
overlook some aspects that are less obvious to people who haven’t worked on it
for years.

## Contributing

If you have a patch you think is worth inspecting right away, opening a pull
request without prelude is fine, although I would certainly appreciate an
accompanying explanation of what the patch does and why.

If you have questions, bugs, suggestions, or other contributions of any kind
that do not immediately touch the codebase, you can reach me informally to talk
about them, or open an issue.

I will do my best to respond to all contacts in a timely manner.

## Environment

I use `just` as my command driver. Please use `just format` and `just test` to
keep your modifications consistent with the rest of the project.
