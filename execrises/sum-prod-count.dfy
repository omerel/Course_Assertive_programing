method Main() {
	var a: array<int> := new int[4];
	a[0] := 7;
	a[1] := -2;
	a[2] := 3;
	a[3] := -2;
	assert a[..] == [7,-2,3,-2];

	var s, p, c := SumProdAndCount(a, -2);
	assert a[0] == 7 && a[1] == -2 && a[2] == 3 && a[3] == -2;
	assert s == RecursiveSum(a, 0); // == 6
	assert p == RecursivePositiveProduct(a, 0); // == 21
	assert c == RecursiveCount(-2, a, 0); // == 2
	print "\nThe sum of all elements in [7,-2,3,-2] is ";
	print s;
	print "\nThe product of all positive elements in [7,-2,3,-2] is ";
	print p;
	print "\nThe number of occurrences of -2 in [7,-2,3,-2] is ";
	print c;
}

function RecursiveSum(a: array<int>, from: nat) : int
	reads a
	requires a != null
	requires from <= a.Length
	decreases a.Length-from
{
	if from == a.Length then 0
	else a[from] + RecursiveSum(a, from+1)
}

function RecursivePositiveProduct(a: array<int>, from: nat) : int
	reads a
	requires a != null
	requires from <= a.Length
	decreases a.Length-from
{
	if from == a.Length then 1
	else if a[from] <= 0 then RecursivePositiveProduct(a, from+1)
	else a[from] * RecursivePositiveProduct(a, from+1)
}

function RecursiveCount(key: int, a: array<int>, from: nat) : int
	reads a
	requires a != null
	requires from <= a.Length
	decreases a.Length-from
{
	if from == a.Length then 0
	else if a[from] == key then 1+RecursiveCount(key, a, from+1)
	else RecursiveCount(key, a, from+1)
}

method SumProdAndCount(a: array<int>, key: int) returns (s: int, p: int, c: nat)
	requires a != null
	ensures s == RecursiveSum(a, 0)
	ensures p == RecursivePositiveProduct(a, 0)
	ensures c == RecursiveCount(key, a, 0)
  {
    assert a != null;
    var i : int := 0;
    s,p,c:= 0, 1, 0;
    assert Inv(a,key,i,s,p,c);
    while (i < a.Length)
    invariant Inv(a,key,i,s,p,c);
    {
      s:= s +a[i];
      
      if a[i] == key
      {
        assert a[i] == key;
        c:= c+1;
      }
      else
      { 
      }
      if a[i] > 0
      {
        assert a[i] > 0;
        p:=p*a[i];
      }
      else
      {
      }
      i:= i+1;
      assert Inv(a,key,i,s,p,c);
    }
    assert i == a.Length;
    assert Inv(a,key,i,s,p,c);
    //==>
    assert s == RecursiveSum(a, 0);
    assert p == RecursivePositiveProduct(a, 0);
    assert c == RecursiveCount(key, a, 0);
  }
  
  predicate Inv(a: array<int>, key: int, i: nat,s: int, p: int, c: nat)
	reads a
  requires a != null;
{
	0 <= i <= a.Length &&
  s +  RecursiveSum(a, i) == RecursiveSum(a, 0) &&
  p*RecursivePositiveProduct(a, i) == RecursivePositiveProduct(a, 0) &&
  c + RecursiveCount(key, a, i) == RecursiveCount(key, a, 0)
}
 