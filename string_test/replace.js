var a = J$.readString();
function replace_test(a) {
    if(a === "bbb")
        console.log(1);
    else if (a.replace(/(bbb)(bbb)/g, "$1") === "bbb")
        console.log(2);
}
replace_test(a)