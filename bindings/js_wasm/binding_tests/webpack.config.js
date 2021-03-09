const path = require('path');

const node = {
  entry: "./bootstrap.js",
  target: 'node',
  output: {
    path: path.resolve(__dirname, "dist"),
    filename: 'bootstrap.js',
  },
  mode: "development",
  plugins: [],
};

module.exports = [node];
