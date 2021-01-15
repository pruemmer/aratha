var value1 = J$.readString();
var value2 = J$.readString();
function escapeAttribute(value1,value2) {
    if(/\"/.test(value1)){
        console.log(0);
    }else if(value1 === value2)
        console.log(1);
}
escapeAttribute(value1,value2);