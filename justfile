# https://github.com/casey/just

# build wasm and js bindings
js:
  #!/usr/bin/env bash
  cd bindings/js_wasm
  rm -rf pkg
  wasm-pack build --target nodejs --out-dir pkg --out-name index
  wasm-pack build --target bundler --out-dir pkg --out-name index_bundle
  cp package.json pkg/package.json

# install js test depenedenicies, requires yarn
js-test-init:
  #!/usr/bin/env bash
  cd bindings/js_wasm/binding_tests
  yarn

# run js tests but assume `js-test-init` and `js` were already run
js-test-light:
  #!/usr/bin/env bash
  cd bindings/js_wasm/binding_tests
  yarn test

# run js tests (called from ci)
js-test:
  just js
  just js-test-init
  just js-test-light

# remove dist and node_modules from js bindings tests
clean:
  cargo clean
  cd benches; cargo clean
  rm -rf bindings/js_wasm/pkg
  just clean-js

# remove artifacts from js bindings tests
clean-js:
  rm -rf bindings/js_wasm/binding_tests/dist
  rm -rf bindings/js_wasm/binding_tests/node_modules

bench:
  #!/usr/bin/env bash
  cd benches
  cargo bench

checkall-buildall:
  just clean
  cargo test
  cargo clippy -- -D warnings
  just bench
  just js-test

assert-clean-workdir:
  ! test -n "$(git status --porcelain)" # please commit before publish

publish-js:
  just checkall-buildall
  just assert-clean-workdir
  cd bindings/js_wasm/pkg && npm publish

publish-rs:
  just checkall-buildall
  just assert-clean-workdir
  cargo publish
