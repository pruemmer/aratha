a = J$.readString()

function test_search(a) {
    if(a.search("foo") >= 0)
        console.log(1)
    else
        console.log(2)
}

test_search(a)