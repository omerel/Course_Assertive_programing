method Main() {
	var p := PositiveProduct([8,9]);
	assert p == 72;
	print "\nThe product of all positive elements in [8,9] is ";
	print p;
}

function RecursivePositiveProduct(q : seq<int>) : nat
{
	if q == [] then 1
	else if q[0] <= 0 then RecursivePositiveProduct(q[1..])
	else q[0]*RecursivePositiveProduct(q[1..])
}

// Loop
method PositiveProduct(q : seq<int>) returns (p : nat)
	ensures p == RecursivePositiveProduct(q)
  {
    var i:nat := |q|;
    p := 1;
    assert p == RecursivePositiveProduct(q[i..]);
    while i != 0
      invariant 0 <= i <= |q|
      invariant p == RecursivePositiveProduct(q[i..])
    {
      i := i - 1;
      if q[i] > 0
      {
        p := p * q[i];
        assert p == RecursivePositiveProduct(q[i..]);
      }
      else
      {
        assert p == RecursivePositiveProduct(q[i..]);
      }
      assert p == RecursivePositiveProduct(q[i..]);
    }
    assert p == RecursivePositiveProduct(q);
  }

  // Recursive
  method PositiveProduct(q : seq<int>) returns (p : nat)
	ensures p == RecursivePositiveProduct(q)
  {
    if q == []
    {
      p := 1;
      assert p == RecursivePositiveProduct(q);
    }
    else
    {
      if (q[0] > 0)
      {
        var temp := PositiveProduct(q[1..]);
         p := q[0]*temp;
      }
      else
      {
        var temp := PositiveProduct(q[1..]);
        p := 1*temp;
      }
    }
  }