var failure = null;

function successCont(state) {
	return state;
}

function passMatcher(x, c) {
	return c(x);
}

function newSubpatternState(state) {
	return {
		start: state.start,
		end: state.end,
		length: 0,
		nCapturingParens: 0,
		flags: state.flags
	};
}

function compile(pattern, self) {
	var s = {
		start: 0,
		end: pattern.length,
		length: 0,
		nCapturingParens: 0,
		flags: {
			ignoreCase: self.ignoreCase,
			multiline: self.multiline
		}
	};
	var m = disjunction(pattern, s);
	if (m === failure || s.start + s.length !== s.end)
		throw new SyntaxError();
	return function(str, index) {
		var input = str;
		var inputLength = input.length;
		var c = successCont;
		var cap = new Array(s.nCapturingParens);
		var x = {endIndex: index, captures: cap, input: str};
		return m(x, c);
	};
}

function disjunction(pattern, state) {
	var s = newSubpatternState(state);
	var m = alternative(pattern, s);
	if (m === failure)
		return failure;
	if ( s.start + s.length === s.end || pattern.substr(s.start + s.length, 1) !== '|' ) {
		state.length = s.length;
		state.nCapturingParens += s.nCapturingParens;
		return m;
	}
	var t = newSubpatternState(state);
	t.start += s.length + 1;
	var m2 = disjunction(pattern, t);
	if (m2 === failure) {
		state.length = s.length;
		state.nCapturingParens += s.nCapturingParens;
		return m;
	}
	state.length = s.length + 1 + t.length;
	state.nCapturingParens += s.nCapturingParens + t.nCapturingParens;
	return function(x, c) {
		var r = m(x, c);
		if (r !== failure)
			return r;
		return m2(x, c);
	};
}

function alternative(pattern, state) {
	var result = passMatcher;
	var start = 0;
	var s = newSubpatternState(state);
	var m2 = term(pattern, s);
	while( m2 !== failure ) {
		state.length += s.length;
		state.nCapturingParens += s.nCapturingParens;
		result = function(m1, m2) {
			return function(x, c) {
				var d = function(y) { return m2(y, c); };
				return m1(x, d);
			};
		}(result, m2);
		start = s.start + s.length;
		s = newSubpatternState(state);
		s.start = start;
		m2 = term(pattern, s);
	}
	return result;
}

function term(pattern, state) {
	var s = newSubpatternState(state);
	var t = assertion(pattern, s);
	if ( t !== failure ) {
		state.length = s.length;
		state.nCapturingParens += s.nCapturingParens;
		return function(x, c) {
			var r = t(x);
			if (r === false)
				return failure;
			return c(x);
		};
	}
	s = newSubpatternState(state);
	var m = atom(pattern, s);
	if ( m === failure )
		return failure;
	var s2 = newSubpatternState(state);
	s2.start += s.length;
	var q = quantifier(pattern, s2);
	if ( q === failure ) {
		state.length = s.length;
		state.nCapturingParens += s.nCapturingParens;
		return m;
	}
	var min = q.min, max = q.max, greedy = q.greedy;
	if ( isFinite( max ) && max < min )
		throw new SyntaxError();
	var parenIndex = state.nCapturingParens;
	var parenCount = s.nCapturingParens;
	state.length = s.length + s2.length;
	state.nCapturingParens += s.nCapturingParens;
	return function(x, c) {
		return repeatMatcher(m, min, max, greedy, x, c, parenIndex, parenCount);
	};
}

function repeatMatcher(m, min, max, greedy, x, c, parenIndex, parenCount) {
	if (max === 0)
		return c(x);
	var d = function(y) {
		if (min === 0 && y.endIndex === x.endIndex)
			return failure;
		var min2 = min === 0 ? 0 : min - 1;
		var max2 = max === Infinity ? max : max - 1;
		return repeatMatcher(m, min2, max2, greedy, y, c, parenIndex, parenCount);
	};
	var cap = x.captures.slice(0);
	for (var k = parenIndex; k < parenIndex + parenCount; ++k)
		cap[k] = undefined;
	var e = x.endIndex;
	var xr = {endIndex: e, captures: cap, input: x.input};
	if ( min !== 0 )
		return m(xr, d);
	var z;
	if ( greedy ) {
		z = m(xr, d);
		if ( z !== failure )
			return z;
		return c(x);
	}
	z = c(x);
	if ( z !== failure )
		return z;
	return m(xr, d);
}

function assertion(pattern, state) {
	if (state.start + 1 <= state.end && pattern.substr(state.start, 1) === '^') {
		state.length = 1;
		return function(x) {
			var e = x.endIndex;
			if (e === 0)
				return true;
			if (state.flags.multiline === true && /[\x0a\x0d\u2028\u2029]/.test(x.input.substr(e-1,1)))
				return true;
			return false;
		};
	}
	if (state.start + 1 <= state.end && pattern.substr(state.start, 1) === '$') {
		state.length = 1;
		return function(x) {
			var e = x.endIndex;
			if (e === x.input.length)
				return true;
			if (state.flags.multiline === true && /[\x0a\x0d\u2028\u2029]/.test(x.input.substr(e,1)))
				return true;
			return false;
		};
	}
	if (state.start + 2 <= state.end && pattern.substr(state.start, 2) === '\\b') {
		state.length = 2;
		return function(x) {
			return isWordChar(x, x.endIndex - 1) !== isWordChar(x, x.endIndex);
		}
	}
	if (state.start + 2 <= state.end && pattern.substr(state.start, 2) === '\\B') {
		state.length = 2;
		return function(x) {
			return isWordChar(x, x.endIndex - 1) === isWordChar(x, x.endIndex);
		}
	}
	return failure;
}

function isWordChar(x, e) {
	return e !== -1 && e !== x.input.length && /\w/.test(x.input.substr(e,1));
}

function quantifier(pattern, state) {
	var min, max, greedy;
	q: {
		if (state.start + 1 <= state.end)
			switch( pattern.substr(state.start, 1) ) {
				case '*':
					state.length = 1, min = 0, max = Infinity;
					break q;
				case '+':
					state.length = 1, min = 1, max = Infinity;
					break q;
				case '?':
					state.length = 1, min = 0, max = 1;
					break q;
			};
		var r = pattern.substring(state.start, state.end).match(/^\{(\d+)(,(\d+)?)?\}/);
		if ( r === null )
			return failure;
		min = parseInt(r[1], 10);
		max = r[2] === undefined ? min : (r[3] === undefined ? Infinity : parseInt(r[3], 10));
		state.length = r[0].length;
	}
	if (state.start + state.length < state.end && pattern.substr(state.start, 1) === '?')
		return (state.length += 1, {min: min, max: max, greedy: false});
	return {min: min, max: max, greedy: true};
}

function atom(pattern, state) {
	var flags = "";
	if ( state.start < state.end && /[^^$\\.*+?()\[\]{}\|]/.test(pattern.substr(state.start, 1)) ) {
		state.length += 1;
		if ( state.flags.ignoreCase )
			flags += 'i';
		if ( state.flags.multiline )
			flags += 'm';
		return characterSetMatcher(new RegExp(pattern.substr(state.start, 1), flags));
	}
	if ( state.start < state.end && pattern.substr(state.start, 1) === '.') {
		state.length += 1;
		if ( state.flags.ignoreCase )
			flags += 'i';
		if ( state.flags.multiline )
			flags += 'm';
		return characterSetMatcher(/./);
	}
	var s, m;
	if ( state.start < state.end && pattern.substr(state.start, 1) === "\\" ) {
		s = newSubpatternState(state);
		s.start += 1;
		m = atomEscape(pattern, s);
		if ( m !== failure ) {
			state.length = 1 + s.length;
			state.nCapturingParens += s.nCapturingParens;
			return m;
		}
	}
	s = newSubpatternState(state);
	var t = characterClass(pattern, s);
	if ( t !== failure ) {
		state.length = s.length;
		state.nCapturingParens += s.nCapturingParens;
		return characterSetMatcher(t);
	}
	var parenIndex;
	if ( state.start + 1 <= state.end - 1 && /\([^?]/.test(pattern.substr(state.start, 2)) ) {
		s = newSubpatternState(state);
		s.start += 1;
		s.end -= 1;
		parenIndex = state.nCapturingParens;
		m = disjunction(pattern, s);
		if ( m !== failure && pattern.substr(s.start + s.length, 1) === ')' ) {
			state.length = 1 + s.length + 1;
			state.nCapturingParens += 1 + s.nCapturingParens;
			return function(x, c) {
				var d = function(y) {
					var cap = y.captures.slice(0);
					var xe = x.endIndex;
					var ye = y.endIndex;
					cap[parenIndex] = y.input.substring(xe, ye);
					return c({endIndex: ye, captures: cap, input: y.input});
				};
				return m(x, d);
			};
		}
	}
	if ( state.start + 3 <= state.end - 1 && pattern.substr(state.start, 3) === "(?:" ) {
		s = newSubpatternState(state);
		s.start += 3;
		s.end -= 1;
		m = disjunction(pattern, s);
		if ( m !== failure && pattern.substr(s.start + s.length, 1) === ')' ) {
			state.length = 3 + s.length + 1;
			state.nCapturingParens += s.nCapturingParens;
			return m;
		}
	}
	if ( state.start + 3 <= state.end - 1 && pattern.substr(state.start, 3) === "(?=" ) {
		s = newSubpatternState(state);
		s.start += 3;
		s.end -= 1;
		m = disjunction(pattern, s);
		if ( m !== failure && pattern.substr(s.start + s.length, 1) === ')' ) {
			state.length = 3 + s.length + 1;
			state.nCapturingParens += s.nCapturingParens;
			return function(x, c) {
				var r = m(x, successCont);
				if ( r === failure )
					return failure;
				return c({endIndex: x.endIndex, captures: r.captures, input: x.input});
			};
		}
	}
	if ( state.start + 3 <= state.end - 1 && pattern.substr(state.start, 3) === "(?!" ) {
		s = newSubpatternState(state);
		s.start += 3;
		s.end -= 1;
		m = disjunction(pattern, s);
		if ( m !== failure && pattern.substr(s.start + s.length, 1) === ')' ) {
			state.length = 3 + s.length + 1;
			state.nCapturingParens += s.nCapturingParens;
			return function(x, c) {
				var r = m(x, successCont);
				if ( r !== failure )
					return failure;
				return c(x);
			};
		}
	}
	return failure;
}

function characterSetMatcher(tester) {
	return function(x, c) {
		var e = x.endIndex;
		if ( e === x.input.length )
			return failure;
		if ( !tester.test( x.input.substr(e, 1) ) )
			return failure;
		return c({endIndex: e + 1, captures: x.captures, input: x.input});
	};
}

function atomEscape(pattern, state) {
	var s = newSubpatternState(state);
	var E = decimalEscape(pattern, s);
	var flags = (state.flags.ignoreCase ? 'i' : '') + (state.flags.multiline ? 'm' : '');
	var m, n;
	if ( E !== failure ) {
		state.length = s.length;
		m = characterSetMatcher(new RegExp(pattern.substr(state.start-1,state.length+1)), flags);
		if ( typeof E ==='string' )
			return m;
		n = E;
		return function(x, c) {
			var cap = x.captures;
			if ( n === 0 || n > cap.length )
				return m(x, c);
			var s = cap[n - 1];
			if ( s === undefined )
				return c(x);
			var e = x.endIndex;
			var len = s.length;
			var f = e + len;
			if (f > x.input.length)
				return failure;
			if (!new RegExp(s.replace(/[\^$\\.*+?()\[\]{}\|]/g, "\\$&"), flags).test(x.input.substr(e, len)))
				return failure;
			return c({endIndex: f, captures: cap, input: x.input});
		};
	}
	var r = pattern.substring(state.start, state.end).match(/^[tnvfr]|c[a-zA-Z]?|x[0-9a-fA-Z]{2}|u[0-9a-fA-Z]{4}|[dDsSwW]|[\d\D]/);
	if ( r !== null ) {
		state.length = r[0].length;
		return characterSetMatcher(new RegExp(pattern.substr(state.start-1,state.length+1)), flags);
	}

	return failure;
}

function decimalEscape(pattern, state) {
	var r = pattern.substring(state.start, state.end).match(/^\d+/);
	if ( r === null )
		return failure;
	state.length = r[0].length;
	var i = parseInt(r[0], 10);
	if ( i === 0 )
		return '\x00';
	return i;
}

function characterClass(pattern, state) {
	var p = pattern.substring(state.start, state.end).match(/^\[(?:[^\\\]]|\\[\d\D])*\]/);
	if ( p === null )
		return failure;
	var e, t;
	try {
		t = new RegExp(p[0], (state.flags.ignoreCase ? 'i' : ''));
	} catch ( e ) {
		throw e;
	}
	state.length = p[0].length;
	return t;
}


compile = (function(compile) {
	return function() {
		var e;
		try {
			return compile.apply(this, arguments);
		} catch (e) {
			if ( e instanceof SyntaxError )
				throw new Error('cntexp SyntaxError');
			throw e;
		}
	};
})(compile);


exports.compile = compile;
