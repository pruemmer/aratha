var arg = J$.readString();

function test_match(digitsInfo){
    if (digitsInfo) {
        var parts = digitsInfo.match(/^(\d+)?\.((\d+)(-(\d+))?)?$/);
        if (parts !== null) {
            if(/[\\\<\'\"\}\)\>]+/.test(parts[1])) console.log(1);
            if(/[\\\<\'\"\}\)\>]+/.test(parts[3])) console.log(2);
            if(/[\\\<\'\"\}\)\>]+/.test(parts[5])) console.log(3);
		}
		else console.log(0);
    }
}
test_match(arg)