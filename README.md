# Valinor

Valhalla 🤝 🦀

To continue the mythological theme, this project is cheekily named [Valinor](https://en.wikipedia.org/wiki/Valinor).

## Intro

**Preface:** this project available as-is.
We use this code for various purposes internally,
and it is probably only useful if you're already a skilled Valhalla hacker.

That said, there are a few reasons we'd like to see such a project exist,
so we're open sourcing this code.

Here are a few things that we think are worth exploring:

* Making it easier to build tooling around Valhalla by offering a safe, fast interface
* Improving the ergonomics of routing on mobile (eventually via UniFFI)
* Finding ways to improve graph tile generation with better parallelism, support for alternate data formats (e.g. parquet), and a more understandable mapping system
* Building a safer dynamic costing model system that's plugin-based (ex: via WASM components),
  which are unlikely to be merged into the upstream codebase anytime soon;
  as of this writing, C++ is not capable of serving as a WASM Component Host
* Improving the quality and safety of Valhalla (reimplementations tend to identify bugs in the original)
* Simplifying the process of building Valhalla microservices (see [valhalla-microservice](valhalla-microservice))

If you're interested in collaborating, please get in touch!

## Building the project

If you check out the repo and build with cargo, all should "just work."
However, it's more likely than not that you'd like to use this in a library.
At the moment, we rely on an unstable feature of zerocopy due to underspecified behavior of bit copies of unions.
See [this discussion](https://github.com/google/zerocopy/discussions/1802) for details.

TL;DR, you'll need to set a config flag.
We do it like this in `.cargo/config.toml`:

```toml
[build]
rustflags = ["--cfg", "zerocopy_derive_union_into_bytes"]
```

This enables the project to build when checked out directly, but if you're depending on it as a library,
you need to do this in your project too!

## Misc

* Nearly all tests (barring those which use unsupported syscalls) are run under miri to screen for UB.
* Platform support:
  * We test every PR on Linux, macOS, and Windows
  * We also test on a big-endian emulator
  * In theory any platform with Rust std support should work,
    but some features like the tarball memory mapper require 64-bit atomics.
  * `no-std` isn't an explicit target yet, but reach out if you're interested.