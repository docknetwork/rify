const path = require("path");
const webpack = require("webpack");
const cloneDeep = require("clone-deep");
const CopyPlugin = require("copy-webpack-plugin");
const WasmPackPlugin = require("@wasm-tool/wasm-pack-plugin");

const dist = path.resolve(__dirname, "dist");
const pkg = path.resolve(__dirname, "pkg");

const webpackConf = {
  mode: "production",
  entry: {
    index: "./js/index.js"
  },
  output: {
    path: dist,
    filename: "[name].js",
    // libraryTarget: 'commonjs2',
    // libraryTarget: 'var',
    library: 'rify'
  },
  // optimization: {
  //   splitChunks: {
  //     chunks (chunk) {
  //       return false;
  //     }
  //   }
  // },
  devServer: {
    contentBase: dist,
  },
};

module.exports = [
  // NodeJS output to pkg/index.js
  // need separate nodejs/web files
  // (because nodejs uses fs/path modules)
  {
    mode: "production",
    target: 'node',
    entry: {
      index: "./js/index.js"
    },
    output: {
      path: dist,
      filename: "[name]-throwaway.js",
      // libraryTarget: 'commonjs2',
      // libraryTarget: 'var',
      library: 'rify'
    },
    plugins: [
      new webpack.optimize.LimitChunkCountPlugin({
        maxChunks: 1
      }),
      new WasmPackPlugin({
        outDir: 'pkg',
        crateDirectory: __dirname,
        extraArgs: "--target nodejs --mode normal",
      }),
    ]
  },

  // Object.assign(cloneDeep(webpackConf), {
  //   target: 'node',
  //   output: {
  //     libraryTarget: 'umd',
  //     globalObject: 'this',
  //   },
  //   plugins: [
  //     new webpack.optimize.LimitChunkCountPlugin({
  //       maxChunks: 1
  //     }),
  //     new WasmPackPlugin({
  //       outDir: 'pkg',
  //       crateDirectory: __dirname,
  //       extraArgs: "--target nodejs --mode normal",
  //     }),
  //   ]
  // }),

  // Theoretically if WASM is inlined it should work
  // in node js too... but webpack adds references to document to load chunk script
  Object.assign(cloneDeep(webpackConf), {
    entry: {
      index: "./js/index-web.js"
        // index: "./pkgweb/index.js"
    },
    output: {
	  	webassemblyModuleFilename: "index_bg.wasm",
      libraryTarget: 'umd',
      filename: "[name]-web.js",
      globalObject: 'this',
    },
  	module: {
  		rules: [
  			{
  				test: /\.wasm$/,
  				type: "webassembly/experimental"
  			}
  		]
  	},
    plugins: [
      // Would like to use this to remove 1-web.js but then no wasm file is copied
      // new webpack.optimize.LimitChunkCountPlugin({
      //   maxChunks: 1
      // }),
      new WasmPackPlugin({
        outName: 'index_web',
        outDir: 'pkgweb',
        crateDirectory: __dirname,
        extraArgs: "--target bundler --mode normal",
      }),

      // Final step copies some files from last build
      new CopyPlugin([
        {
          from: path.resolve(__dirname, "package-dist.json"),
          to: 'package.json',
        },

        path.resolve(__dirname, "pkg/index.d.ts"),
        path.resolve(__dirname, "pkg/index_bg.wasm.d.ts"),
        path.resolve(__dirname, "pkg/index.js"),
        path.resolve(__dirname, "pkgweb/index_web_bg.wasm"),
        path.resolve(__dirname, "pkg/index_bg.wasm")
      ]),
    ]
  })
];
