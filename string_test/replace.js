var a = J$.readString();
function replace_test(a) {
    if(a === "bbb")
        console.log(1);
    else if (a.replace("a", "b") === "bbb")
        console.log(2);
}
replace_test(a)