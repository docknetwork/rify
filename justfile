js:
	wasm-pack build -- --features js-library-wasm

# install js test depenedenicies, requires yarn
js-test-init:
	cd bindings_tests/rify_js; yarn

# run js tests but assume `js-test-init` and `js` were already run
js-test-light:
	cd bindings_tests/rify_js; npx jest

# run js tests requires npx
js-test:
	just js
	just js-test-init
	just js-test-light
