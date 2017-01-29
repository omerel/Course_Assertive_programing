// Source: Carroll Morgan's "Programming from Specifications", Second edition, Exercise 15.17

// Consider the binary tree type:
datatype BT<T> = Tip(T) | Node(BT<T>, BT<T>)
// The frontier of such a tree is the sequence of tip-values in left-to-right order.
// Your assignment is to develop iterative code that computes the frontier of a given tree
method Main()
{
	var tree: BT<int>;
	tree := Tip(1);
	var f: seq<int> := FrontierIter(tree);
	assert f == [1];

	tree := Node(tree, Tip(2));
	f := FrontierIter(tree);
	assert f == [1,2];
}

function Frontier<T>(tree: BT<T>): seq<T>
{
	match tree {
		case Tip(n) => [n]
		case Node(left, right) => Frontier(left) + Frontier(right)
	}
}

function Fseq<T>(forest:seq<BT<T>>) : seq<T>
{
	if forest == [] then [] else Frontier(forest[0]) + Fseq(forest[1..])
	/*match forest[0]
		case Tip(n) => [n] + Fseq(forest[1..])
		case Node(left, right) => Frontier(left) + Frontier(right) + Fseq(forest[1..])
	*/
}

function ForestSize<T>(stack : seq<BT<T>>): nat
{
	if stack == [] then 0
	else TreeSize(stack[0]) + ForestSize(stack[1..])
}

function TreeSize<T>(tree : BT<T>) : nat
{
	match tree {
		case Tip(n) => 1
		case Node(left, right) => TreeSize(left) + TreeSize(right) + 1
	}
}

method FrontierIter<T>(tree: BT<T>) returns (f: seq<T>)
	ensures f == Frontier(tree)
{
	var stack: seq<BT<T>>;
	stack := [tree];
	f := [];
	// TODO: continue here, computing the frontier of "tree" by iterating its subtrees,
	// all the way to its tips, in the expected order, using the "stack"
	while stack != []
		invariant f + Fseq(stack) == Frontier(tree)
		decreases ForestSize(stack)
	{
	ghost var V0 := ForestSize(stack);
		match stack[0]
			case Tip(n) =>
				f:= f + [n];
				stack := stack[1..];
			case Node(left, right) =>
				stack := [left, right] + stack[1..];
		assert 0 <= ForestSize(stack) < V0;
	}
	assert stack == [] && f + Fseq(stack) == Frontier(tree);
	assert f == Frontier(tree);
}
