var path = require('path');
var webpack = require('webpack');

module.exports = {
    entry: './mock.js',
    output: {
        path: path.resolve(__dirname, 'build'),
        filename: 'runmock.js'
    },
    target: 'node',
    loader: {
        "foo": 'babel-loader'
    },
    module: {
    },
    stats: {
        colors: true
    },
    devtool: 'source-map'
};
