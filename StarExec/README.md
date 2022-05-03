## Building for StarExec

All commands are assumed to be run in the `sat` root directory.

You need to have done:
```
rustup target add x86_64-unknown-linux-musl
```
beforehand.

If you are not on a Linux, you'll probably have to use `cross` og `cargo
zigbuild`.

You can get `cargo zigbuild` by:

```
pip3 install ziglang
cargo install cargo-zigbuild
```

If you are using zigbuild, run:

```
RUSTFLAGS='-C relocation-model=static' cargo zigbuild --release --target x86_64-unknown-linux-musl
```

The following has worked on Linux:

```
RUSTFLAGS='-C relocation-model=static' cargo build --release --target x86_64-unknown-linux-musl
```

And then:

```
cp ./target/x86_64-unknown-linux-musl/release/sat StarExec/bin/creusat
```

Yes, this should be scripted.


