var value = J$.readString();

function fun(value)
{ 
   var value1 = value.replace(/\\([\\\]])/g, '$1');
   if(/\\\\/.test(value1)) console.log("1");
}

fun(value);