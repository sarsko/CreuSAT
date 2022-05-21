## Building for StarExec

The easiest way is to run
```
cargo make StarExec
```
in the root directory. 

That does however currently only work on Linux out of the box.

You need to have done:
```
rustup target add x86_64-unknown-linux-musl
```
beforehand.


If you are not on a Linux, you'll probably have to use `cross` or `cargo
zigbuild`.

You can get `cargo zigbuild` by:

```
pip3 install ziglang
cargo install cargo-zigbuild
```

If you are using zigbuild, run:

```
RUSTFLAGS='-C relocation-model=static' cargo zigbuild --release --target
x86_64-unknown-linux-musl
```

And then:

```
cp ./target/x86_64-unknown-linux-musl/release/sat StarExec/bin/creusat
```



