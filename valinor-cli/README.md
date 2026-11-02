# Valinor CLI

A CLI multi-tool for quickly inspecting Valhalla graphs.
This utility takes a Valhalla JSON configuration as input,
and has subcommands with various functionality.

This is primarily meant as a low-level debugging tool for Valinor developers.
If this looks useful to you, it probably is; otherwise, it's probably not.

## Example: getting edge info

As an example, you can get edge info like this (works with either the integer or slash separated form):

```shell
RUST_LOG=info cargo run --package valinor-cli -- ~/valhalla-docker/valhalla/valhalla.json get-edge 901881911882
```

Then you'll get some JSON output on your terminal with the details.

Run the `help` subcommand for more details (everything is automatically documented via clap).