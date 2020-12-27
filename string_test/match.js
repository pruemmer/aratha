a = J$.readString()

function test_match(a) {
    var FN_ARGS = /(hhh|cccc)(aaaa|bbb)/;
    b = a.match(FN_ARGS);
    if(b !== null)
        console.log(b);
    else
        console.log(1);
}

test_match(a)