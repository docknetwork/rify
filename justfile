# build wasm and js bindings
js:
	wasm-pack build -- --features js-library-wasm

# install js test depenedenicies, requires yarn
js-test-init:
	cd bindings_tests/rify_js; yarn

# run js tests but assume `js-test-init` and `js` were already run
js-test-light:
	cd bindings_tests/rify_js; yarn test

# run js tests
js-test:
	just js
	just js-test-init
	just js-test-light

# remove dist and node_modules from js bindings tests
clean:
	cargo clean
	rm -r pkg || true
	clean-js

# remove artifacts from js bindings tests
clean-js:
	rm -r bindings_tests/rify_js/dist || true
	rm -r bindings_tests/rify_js/node_modules || true
