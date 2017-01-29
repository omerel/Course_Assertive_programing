method Main() {
	var q := [4,8,6,3];
	var p := Product(q);
	print "the product of odd-indexed elements of [4,8,6,3] is ";
	print p;
	assert p == 8 * 3;
	print "\ndone.";
}

function OddIndexedProduct(q: seq<int>) : int
{
	RecursiveOddIndexedProduct(q, 0)
}

function RecursiveOddIndexedProduct(q: seq<int>, i: nat) : int
	requires i <= |q|;
	decreases |q|-i;
{
	if i == |q| then 1
	else if i % 2 == 1 then q[i] * RecursiveOddIndexedProduct(q, i+1)
	else RecursiveOddIndexedProduct(q, i+1)
}

// Loop in the wrong direction
method Product'(q: seq<int>) returns (p: int)
  ensures p == OddIndexedProduct(q)
{
	var i:nat;
	p,i := 1,0;
	while i != |q|
	invariant 0 <= i <= |q| && p == OddIndexedProduct(q[..i])
	{
		assert 0 <= i < |q| && p == OddIndexedProduct(q[..i]);
		if i % 2 ==1
		{
			assert 0 <= i < |q| && p == OddIndexedProduct(q[..i]);
			assert i%2 == 1;
			L1(i,p,q,q[i]);
			assert 0 <= i+1 <= |q| && p*q[i] == OddIndexedProduct(q[..i+1]);
			p,i := p*q[i], i+1;
			assert 0 <= i <= |q| && p == OddIndexedProduct(q[..i]);
		}
		else
		{
			assert 0 <= i < |q| && p == OddIndexedProduct(q[..i]);
			assert i%2 != 1;
			L2(i,p,q,q[i]);
			assert 0 <= i+1 <= |q| && p == OddIndexedProduct(q[..i+1]);
			i := i+1;
			assert 0 <= i <= |q| && p == OddIndexedProduct(q[..i]);
		}
		assert 0 <= i <= |q| && p == OddIndexedProduct(q[..i]);
	}
	assert i == |q|;
	assert q == q[..|q|];
	assert p == OddIndexedProduct(q[..i]);
	// ==>
	assert p == OddIndexedProduct(q);
}

lemma L1(i:nat, p:int,q:seq<int>,p':int)
	requires 0 <= i < |q| && p == OddIndexedProduct(q[..i])
	requires i%2 == 1
	requires p' == q[i]
	ensures 0 <= i+1 <= |q| && p*q[i] == OddIndexedProduct(q[..i+1])
{
	calc {
		OddIndexedProduct(q[..i+1]);
	== { assert q[..i]+[q[i]] == q[..i+1]; }
		OddIndexedProduct(q[..i]+[q[i]]);
	== { L2a(q,i); }
		OddIndexedProduct(q[..i])*q[i];
	==
		p*q[i];
	}

}

lemma L2a(q:seq<int>, i: nat)
	requires i % 2 == 1
	requires 0 <= i < |q|
	ensures OddIndexedProduct(q[..i]+[q[i]]) == OddIndexedProduct(q[..i])*q[i]


lemma L2(i:nat, p:int,q:seq<int>,p':int)
	requires 0 <= i < |q| && p == OddIndexedProduct(q[..i])
	requires i%2 != 1
	requires p' == q[i]
	ensures 0 <= i+1 <= |q| && p == OddIndexedProduct(q[..i+1])


// Loop in the right direction
method Product(q: seq<int>) returns (p: int)
  ensures p == OddIndexedProduct(q)
{
	var i:nat;
	p,i := 1,|q|;
	while i != 0
	invariant 0 <= i <= |q| && p == RecursiveOddIndexedProduct(q, i)
	{
		i := i - 1;
		if i % 2 == 1
		{
			p := p * q[i];
		}
		else
		{
		}
		assert 0 <= i <= |q| && p == RecursiveOddIndexedProduct(q, i);
	}
	assert p == OddIndexedProduct(q);
}