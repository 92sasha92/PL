var naive_fibonacci = function f (n) {
    return (n===0 || n === 1) ? n : f(n-1) + f(n-2);
}

var fibonacci = (function () {
    var memo = [0, 1];
    var fib = function f (n) {
        var result = memo[n];
        if (typeof(result) === "undefined") {
            result = f(n-1) + f(n-2);
            memo[n] = result;
        }
        return result;
    };
    return fib;
})();

// is memo in scope here?
// is memo live in memory here?


//
// ADD YOUR CODE HERE FOR DEFINING MEMOIZE, AND THEN UNCOMMENT THE
// CODE BELOW
//

function memoize(f) {
	var memo = [];
	var memoFuncResult = function g (n) {
        var result = memo[n];
        if (typeof(result) === "undefined") {
            result = f(n);
            memo[n] = result;
        }
        return result;
    };
    return memoFuncResult;
}


/* UNCOMMENT AFTER YOU'VE IMPLEMENTED MEMOIZE */


var cool_fibonacci = memoize(function(n) {
    return (n===0 || n === 1) ? n : cool_fibonacci(n-1) + cool_fibonacci(n-2);
});
console.log(cool_fibonacci(100) + " wow, this was fast!");

