
var constructorFn = J$.readString();
function test(name){
//   if (name.match(/^(.+)(?:-(.+))?$/)  && name.match(/^(.+?)(?:-(.+?))?$/)[1] !=='') {
//     throw new Error('Incorrectly formatted service names');
//  }
  var b=name.match(/foo*/);
  if(b && b[1] === "a")
    console.log(b[1]);
  else
    console.log(2);
}
test(constructorFn);