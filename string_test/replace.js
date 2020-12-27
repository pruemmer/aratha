var a = J$.readString();
function replace_test(a) {
    // if(a === "bbb")
    //     console.log(1);
    // if (a.replace(/a/, "b") === "bbb")
    var c = a.replace(/(bbb)(bbb)/g, "$1");
    // var d = c.replace("b", "jjhhh")
    if (c === "bbb")
        console.log(2);
    else
        console.log(1);
    console.log(d)
}
replace_test(a)