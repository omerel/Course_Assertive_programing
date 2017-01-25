method Main() {
	var c := Count(8, [9,8]);
	assert c == 1;
	print "\nThe number of occurrences of 8 in [9,8] is ";
	print c;
}

function RecursiveCount(key : int, q : seq<int>) : nat
{
	if q == [] then 0
	else if q[|q|-1] == key then 1+RecursiveCount(key, q[..|q|-1])
	else RecursiveCount(key, q[..|q|-1])
}

// Loop
method Count(key : int, q : seq<int>) returns (c : nat)
	ensures c == RecursiveCount(key, q);
{
  var q1 := q;
  assert q1 == q;
  c := 0;
  while( |q1| > 0)
  invariant c + RecursiveCount(key, q1) == RecursiveCount(key, q); 
  { 
    ghost var x := |q1|;
    var n := q1[|q1| -1];
    if ( n == key)
    {
      c := c+1;
      q1 :=  q1[..|q1|-1];
    }
    else
    {
      q1 :=  q1[..|q1|-1];
    }
    assert c + RecursiveCount(key, q1) == RecursiveCount(key, q); 
  }
  assert |q1| == 0;
  assert c +RecursiveCount(key, q1) == RecursiveCount(key, q); 
  // ==>
  assert c == RecursiveCount(key, q); 
}

//Recursive
method Count(key : int, q : seq<int>) returns (c : nat)
	ensures c == RecursiveCount(key, q);
{
  if (q == [])
  {
    c:=0;
    assert c == RecursiveCount(key, q);
  } 
  else
  {
    if (q[|q|-1] == key)
    {
      var temp := Count(key, q[..|q|-1]);
      c := 1 + temp;
    }
    else
    {
      c:= Count(key, q[..|q|-1]);
    }
    assert c == RecursiveCount(key, q);
  }
  // ==>
  assert c == RecursiveCount(key, q); 
}