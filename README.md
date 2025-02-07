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
* Finding ways to improve graph tile generation with better parallelism and incremental updates
* Building a safer dynamic costing model system that's plugin-based (ex: via WASM components),
  which are unlikely to be merged into the upstream codebase anytime soon;
  as of this writing, C++ is not capable of serving as a WASM Component Host
* Improving the quality and safety of Valhalla (reimplementations tend to identify bugs in the original)

If you're interested to collaborate, please get in touch!