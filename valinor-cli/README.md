# Valinor CLI

A CLI multi-tool for quickly inspecting Valhalla graphs.
Most subcommands take a Valhalla JSON configuration as input
(`extract` is the exception; it takes a tile extract tarball or a tile directory directly).

This is primarily meant as a low-level debugging tool for Valinor developers.
If this looks useful to you, it probably is; otherwise, it's probably not.

## Example: getting edge info

As an example, you can get edge info like this (works with either the integer or slash separated form):

```shell
RUST_LOG=info cargo run --package valinor-cli -- get-edge ~/valhalla-docker/valhalla/valhalla.json 901881911882
```

Then you'll get some JSON output on your terminal with the details.

## Example: writing an offline sub-extract

You can write a smaller, fully spec-compliant extract
which contains only some tiles of a source (each tile is `level/tile_id`).
The source can be a tile extract tarball or a tile directory:

```shell
cargo run --package valinor-cli -- extract valhalla-graphtile/fixtures/andorra-tiles.tar andorra-sub.tar --tile 0/3015,1/47701,2/763926
cargo run --package valinor-cli -- extract valhalla-graphtile/fixtures/andorra-tiles andorra-sub.tar --tile 0/3015,1/47701,2/763926
```

A one-line summary (tile count and output size) is printed on stderr.
The output is interchangeable with `valhalla_build_extract` output.
The command writes to a temporary file in the output directory,
and renames it to the output path only when the extract is complete.
So the output path never contains a partial extract.

Run the `help` subcommand for more details (everything is automatically documented via clap).
