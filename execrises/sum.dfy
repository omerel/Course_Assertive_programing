method Main() {
	var s := Sum([8,9]);
	assert s == 17;
	print "\nThe sum of elements in [8,9] is ";
	print s;
}

function RecursiveSum(q : seq<int>) : int
{
	if q == [] then 0
	else q[0]+RecursiveSum(q[1..])
}

// loop version 1
method Sum(q : seq<int>) returns (s : int)
	ensures s == RecursiveSum(q);
  {
    var q1 := q;
    s := 0;
    assert s == 0;
    assert q1 == q;
    while (|q1| != 0 )
    invariant s + RecursiveSum(q1) == RecursiveSum(q);
    {
      s := s + q1[0];
      q1 :=  q1[1..];
      assert s + RecursiveSum(q1) == RecursiveSum(q);
    }
    assert |q1| == 0;
    assert s + RecursiveSum(q1) == RecursiveSum(q);
    // ===>
    assert s == RecursiveSum(q);
  }

// loop version 2
method Sum(q : seq<int>) returns (s : int)
	ensures s == RecursiveSum(q);
	{
		s := 0;
	    var i : nat := 0;
	    assert (0 + RecursiveSum(q[0..])) == RecursiveSum(q);
	    assert (s + RecursiveSum(q[i..])) == RecursiveSum(q);
	    while i < |q|
	      invariant 0 <= i <= |q|
	      invariant (s + RecursiveSum(q[i..])) == RecursiveSum(q)
	  {
	    s := s + q[i];
	    i := i + 1;
	    assert s + RecursiveSum(q[i..]) == RecursiveSum(q);
	  }
	  assert s == RecursiveSum(q);
		}

// Recursive
  method Sum(q : seq<int>) returns (s : int)
	ensures s == RecursiveSum(q);
  {
    if (|q| == 0 )
    {
      assert |q| == 0;
      s := 0;
      assert s == RecursiveSum(q);
    }
    else
    {
      assert |q| != 0; 
      var temp := Sum(q[1..]);
      s := q[0] + temp;
      assert s == RecursiveSum(q);
    }
    assert s == RecursiveSum(q);
  }