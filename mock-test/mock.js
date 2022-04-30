import {argv} from 'process';
import * as clvm_tools_rs from './build/clvm_tools_rs.js';

var sliced_argv = argv.slice(1);
console.log(clvm_tools_rs.jsmock(sliced_argv));
