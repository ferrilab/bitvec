# Bit-Level Access Instructions

This trait extends [`Radium`] in order to manipulate specific bits in an element
according to the crate’s logic. It drives all memory access instructions and is
responsible for translating the bit-selection logic of the [`index`] module into
real effects.

This is blanket-implemented on all types that permit shared-mutable memory
access via the [`radium`] crate. Its use is constrained in the [`store`] module.
It is required to be a publicly accessible symbol, as it is exported in other
traits, but it is a crate-internal item and is not part of the public API. Its
blanket implementation for `<R: Radium>` prevents any other implementations from
being written.

[`Radium`]: radium::Radium
[`index`]: crate::index
[`radium`]: radium
[`store`]: crate::store
