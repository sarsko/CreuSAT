#curl --location --remote-header-name --remote-name https://raw.githubusercontent.com/creusot-rs/creusot/master/ci/rust-toolchain && \
curl --location --remote-header-name --remote-name https://raw.githubusercontent.com/creusot-rs/creusot/master/prelude/prelude.mlw && mv prelude.mlw prelude/prelude.mlw && \
curl --location --remote-header-name --remote-name https://raw.githubusercontent.com/creusot-rs/creusot/master/prelude/seq_ext.mlw && mv seq_ext.mlw prelude/seq_ext.mlw && \
commit=$(git ls-remote git@github.com:creusot-rs/creusot.git HEAD  | awk '{ print substr($1,1,8) }')
for C in $(find . -name "Cargo.toml")
do 
    sed -i '' -e "s/rev = \".*\"/rev = \"$commit\"/g" $C
done