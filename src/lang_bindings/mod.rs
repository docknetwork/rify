#[cfg(feature = "js-library-wasm")]
pub mod js_wasm;

#[cfg(test)]
mod js_wasm_test;

// In the future we may export other sorts of bindings e.g. using pyo3.
