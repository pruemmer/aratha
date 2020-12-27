a = J$.readString()

function test_match(a) {
    b = a.match(/foo*/);
    if(b !== null)
        console.log(b[0]);
    else
        console.log(1);
}

test_match(a)