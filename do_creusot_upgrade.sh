curl --location --remote-header-name --remote-name https://raw.githubusercontent.com/xldenis/creusot/master/ci/rust-toolchain && \
curl --location --remote-header-name --remote-name https://raw.githubusercontent.com/xldenis/creusot/master/prelude/prelude.mlw && mv prelude.mlw prelude/prelude.mlw && \
curl --location --remote-header-name --remote-name https://raw.githubusercontent.com/xldenis/creusot/master/prelude/seq_ext.mlw && mv seq_ext.mlw prelude/seq_ext.mlw && \
commit=$(git ls-remote git@github.com:xldenis/creusot.git HEAD  | awk '{ print substr($1,1,8) }')
for C in $(find . -name "Cargo.toml")
do 
    sed -i '' -e "s/rev = \".*\"/rev = \"$commit\"/g" $C
done