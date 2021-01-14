// can not be supported now because of the limitation of ostrich

a = J$.readString();

function test_exec(a) {
    b = /foo*/.exec(a);
    if (b !== null)
        console.log(1);
    else
        console.log(2);
}

test_exec(a)