function test_match(text){
    const shebangPattern = /^#!([^\r\n]+)/u;
    const shebangMatched = text.match(shebangPattern);
    if (shebangMatched && shebangMatched[1].length > 2) {
        console.lgo("1");
    }
    
    }
var a = J$.inputString();
test_match(a);