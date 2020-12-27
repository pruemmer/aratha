tag = J$.readString();

function test(tag){
  var result = '';
  if (tag) {
    result = tag.replace(/(vue\-component\-\d+\-)/g, '$1');
    if(result!=='') console.log("1");   
  }
}
test(tag);