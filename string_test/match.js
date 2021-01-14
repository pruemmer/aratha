a = J$.readString()

function test_match(a) {
    b = a.match(/(foo)*/);
    if(b !== null && b[0] === "foo")
        console.log(b[0]);
    else
        console.log(1);
}

test_match(a)