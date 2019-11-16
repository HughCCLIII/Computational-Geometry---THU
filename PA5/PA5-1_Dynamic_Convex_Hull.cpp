/*

算法思路：

分成上下凸包，当存在竖直边时，规定左边的竖直边属于上凸包，右边的竖直边属于下凸包（竖直边最多两条）

如果不考虑竖直边，那么所有通过凸包上的点的竖直线，将平面分成了一个个slab，首先查找待查询的点位于哪一个slab，然后和这个slab的左右端点连成的线进行一次to-left测试，可确定待查询点在凸包内还是外部。

同时落在上下凸包内部的点就是落在整个凸包内部的点，如果遇到落在凸包外部的点，那么需要更新整个凸包的结构，可以先找到新插入的点和旧凸包相切的两个点（切点是其左右两个点位于切线同侧的点），这两个点之间的在旧凸包上的点需要替换成新插入的点。可以从查询到的slab向左右深入来找到切点，需要注意切点可能一个位于上凸包，一个位于下凸包（这种情况只可能在新插入点位于两个无界的slab时才可能发生）

实现要点及遇到问题：
1. 上下凸包本质上是相同的结构（旋转对称），因此可以进行代码复用。
2. 正确处理共线情形
3. OJ上最后几组测例数据量很大，于是我自己构造出了比较极限的情形用于本地测试（generateToughCase)，以辅助进行代码优化。首先需要确定什么样的测例是计算量最大的，在插入新的点时，可能会引发树中m个元素的删除，单次操作复杂度O(mlogn)，最坏情况O(nlogn)，但是仔细分析这种情况不会连续发生，对于一个测例总计算量最多也不过是向树中插入n个元素以及将这些元素逐个删除的时间。因此测例的计算量主要还是在于树中元素n的个数，而与是否存在这种连续删除情形关系不大。那么如何在有限的坐标范围内构造一个点尽可能多的凸包呢？凸包上的所有线段的斜率都必须不同，因此可以将分母不超过k的所有真分数及它们的倒数进行排序，然后作为这些线段的斜率，最后取一个尽可能大的k就行了（OJ数据的实际坐标范围并不是-1e6~1e6，经测试不超过-1e9~1e9。k取600的时候，可以得到一个点数在88万左右的凸包，用这个进行性能测试应该够了）。

4. OJ数据对Splay Tree不友好，后换用AVL Tree，本地测试两者在大数据下Splay Tree只是略慢



*/


#include<iostream>
#include<cassert>
#include<type_traits>

//#define DEBUG

#ifdef DEBUG
#include<fstream>
#include<vector>
#include<set>
#include<algorithm>
#include<random>
#include<memory>
#include<ctime>
#include<numeric>
using std::unique_ptr;
using std::set;
using std::vector;
using std::set;
#endif // DEBUG


using std::endl;
using std::cin;
using std::cout;
using CoordType = long long int;

struct Point
{
	CoordType x, y;
	Point(CoordType _x = 0, CoordType _y = 0) :x(_x), y(_y)
	{

	}
	Point operator+(const Point& other) const
	{
		return Point(this->x + other.x, this->y + other.y);
	}

	Point operator-(const Point& other) const
	{
		return Point(this->x - other.x, this->y - other.y);
	}

	Point operator*(CoordType t) const
	{
		return Point(this->x * t, this->y*t);
	}

	Point operator/(CoordType t) const
	{
		return Point(this->x / t, this->y / t);
	}

	Point operator-() const
	{
		return Point(-x, -y);
	}

	Point operator+() const
	{
		return Point(x, y);
	}

	bool operator==(const Point& other) const
	{
		return this->x == other.x && this->y == other.y;
	}

	bool operator<(const Point& other) const
	{
		return this->y > other.y || this->y == other.y && this->x < other.x;
	}

	CoordType dot(const Point& other) const
	{
		return x * other.x + y * other.y;
	}
	CoordType cross(const Point& other) const
	{
		return x * other.y - y * other.x;
	}

};

template<typename Key, typename Comp = std::less<Key>>
class SplayTree
{
public:
	struct TreeNode
	{
		TreeNode *lc, *rc;
		TreeNode *parent;
		Key k;
		TreeNode(const Key& k_) :k(k_), lc(nullptr), rc(nullptr), parent(nullptr) {}
	};

	int sz = 0;
	int depthLast = 0;
	int depthFirst = 0;
private:
	Comp comp;
	TreeNode *root;
	TreeNode *minNode, *maxNode;

private:
	template<TreeNode* TreeNode::* p1, TreeNode* TreeNode::* p2>
	void rotate(TreeNode* node)		//make sure that the node always has a parent
	{
		TreeNode *p = node->parent;
		root = root == p ? node : root;
		node->parent = p->parent;
		if (p->parent)
		{
			if (p == p->parent->lc)
			{
				p->parent->lc = node;
			}
			else
			{
				p->parent->rc = node;
			}
		}
		TreeNode* temp = node->*p1;
		node->*p1 = p;
		p->parent = node;
		p->*p2 = temp;
		if (temp)
		{
			temp->parent = p;
		}
	}

	void rightRotate(TreeNode* node)
	{
		rotate<&TreeNode::rc, &TreeNode::lc>(node);
	}
	void leftRotate(TreeNode* node)
	{
		rotate<&TreeNode::lc, &TreeNode::rc>(node);
	}


	void splay(TreeNode* node)
	{
		if (node->parent)
		{
			TreeNode* p = node->parent;
			if (p->parent)
			{
				if (p == p->parent->lc)
				{
					if (node == p->lc)
					{
						rightRotate(p);
						rightRotate(node);
					}
					else
					{
						leftRotate(node);
						rightRotate(node);
					}
				}
				else
				{
					if (node == p->rc)
					{
						leftRotate(p);
						leftRotate(node);
					}
					else
					{
						rightRotate(node);
						leftRotate(node);
					}

				}
				splay(node);
			}
			else
			{
				if (node == p->lc)
				{
					rightRotate(node);
				}
				else
				{
					leftRotate(node);
				}
			}
		}
	}

	void postOrderFree(TreeNode* node)		//stack overflow happens here when the tree is terribly unbalanced
	{
		if (node)
		{
			if (node->lc)
				postOrderFree(node->lc);
			if (node->rc)
				postOrderFree(node->rc);
			delete node;
		}
	}

	template<TreeNode* TreeNode::* p1, TreeNode* TreeNode::* p2>
	TreeNode* neighbour(TreeNode* node)
	{
		TreeNode* ret;
		if (node->*p1)
		{
			ret = node->*p1;
			while (ret->*p2)
			{
				ret = ret->*p2;
			}
			return ret;
		}
		ret = node;
		while (ret->parent && ret->parent->*p1 == ret)
		{
			ret = ret->parent;
		}
		return ret->parent ? ret->parent : nullptr;
	}

	TreeNode* find(const Key& k)		//if not found, return the last node visited
	{
		TreeNode* cursor = root;
		TreeNode* last = cursor;
		while (cursor)
		{
			last = cursor;
			if (comp(cursor->k, k))
			{
				cursor = cursor->rc;
			}
			else if (comp(k, cursor->k))
			{
				cursor = cursor->lc;
			}
			else
			{
				return cursor;
			}
		}
		return last;
	}

public:
	SplayTree() :root(nullptr), minNode(nullptr), maxNode(nullptr)
	{

	}

	~SplayTree()
	{
		postOrderFree(root);
	}

	TreeNode* predecessor(TreeNode* node)
	{
		return neighbour<&TreeNode::lc, &TreeNode::rc>(node);
	}

	TreeNode* successor(TreeNode* node)
	{
		return neighbour<&TreeNode::rc, &TreeNode::lc>(node);
	}

	TreeNode* search(const Key& k)
	{
		TreeNode *ret = find(k);
		splay(ret);
		return ret;
	}

	void insert(const Key& k)
	{
		++sz;
		TreeNode* newNode = new TreeNode(k);
		if (!root)
		{
			root = minNode = maxNode = newNode;
			return;
		}
		TreeNode* temp = find(k);

		newNode->parent = temp;
		if (comp(k, temp->k))
		{
			if (temp == minNode)
			{
				minNode = newNode;
			}
			temp->lc = newNode;
		}
		else
		{
			if (temp == maxNode)
			{
				maxNode = newNode;
			}
			temp->rc = newNode;
		}
		splay(newNode);
	}

	void removeByKey(const Key& k)
	{
		removeByPtr(find(k));
	}

	void removeByPtr(TreeNode* node)
	{
		--sz;
		splay(node);

		if (!root->lc)
		{
			if (root->rc)
			{
				minNode = successor(root);
				root = root->rc;
				root->parent = nullptr;
			}
			else
			{
				root = nullptr;
			}
			delete node;
			return;
		}
		if (!root->rc)
		{
			maxNode = predecessor(root);
			root = root->lc;
			root->parent = nullptr;
			delete node;
			return;
		}

		if (node == minNode)
		{
			minNode = successor(node);
		}
		else if (node == maxNode)
		{
			maxNode = predecessor(node);
		}

		root = node->lc;
		node->lc->parent = nullptr;
		TreeNode *temp = node->lc;
		while (temp->rc)
		{
			temp = temp->rc;
		}
		splay(temp);
		temp->rc = node->rc;
		node->rc->parent = temp;
		delete node;
	}

	TreeNode* lowerBound(const Key& k)		//different from std::lower_bound in semantics; return the greatest element whose key is no greater than 'k', if not found, return nullptr
	{
		TreeNode* node = find(k);
		if (comp(k, node->k))
		{
			return predecessor(node);
		}
		return node;
	}

	TreeNode* first()
	{
		/*TreeNode* ret = root;
		while (ret->lc)
		{
			ret = ret->lc;
			++depthFirst;
		}

		return ret;*/

		return minNode;
	}

	TreeNode* last()
	{
		/*
		TreeNode* ret = root;
		while (ret->rc)
		{
			ret = ret->rc;
			++depthLast;
		}
		return ret;
		*/

		return maxNode;
	}

#ifdef DEBUG
	int inOrderTraversal(vector<Key>& outVec, TreeNode* node)
	{
		int h = 0;
		if (node->lc)
		{
			h = inOrderTraversal(outVec, node->lc);
		}
		outVec.emplace_back(node->k);
		if (node->rc)
		{
			h = std::max(h, inOrderTraversal(outVec, node->rc));
		}
		return h + 1;
	}

	int serialize(vector<Key>& outVec)
	{
		return inOrderTraversal(outVec, root);
	}
#endif // DEBUG
};

template<typename Key, typename Comp = std::less<Key>>
class AVLTree
{
public:
	struct TreeNode;
private:
	static TreeNode* nullNode;
public:
	struct TreeNode
	{
		int h;
		TreeNode *lc, *rc;
		TreeNode *parent;
		Key k;
		TreeNode(const Key& k_, int h_) :k(k_), h(h_), lc(nullNode), rc(nullNode), parent(nullNode) {}
	};

private:
	
	Comp comp;
	TreeNode *root;

	TreeNode* rebalance(TreeNode* cur, TreeNode* p, TreeNode* gp)
	{
		TreeNode *newTop;
		TreeNode *ggp = gp->parent;
		if (p == gp->lc)
		{
			if (cur == p->lc)
			{
				reconstruction34(cur, p, gp, cur->lc, cur->rc, p->rc, gp->rc);
				newTop = p;
			}
			else
			{
				reconstruction34(p, cur, gp, p->lc, cur->lc, cur->rc, gp->rc);
				newTop = cur;
			}
		}
		else
		{
			if (cur == p->lc)
			{
				reconstruction34(gp, cur, p, gp->lc, cur->lc, cur->rc, p->rc);
				newTop = cur;
			}
			else
			{
				reconstruction34(gp, p, cur, gp->lc, p->lc, cur->lc, cur->rc);
				newTop = p;
			}
		}

		if (root == gp)
		{
			root = newTop;
			newTop->parent = nullNode;
		}
		else
		{
			newTop->parent = ggp;
			if (ggp->lc == gp)
			{
				ggp->lc = newTop;
			}
			else
			{
				ggp->rc = newTop;
			}
		}

		return newTop;
	}

	void reconstruction34(TreeNode* a, TreeNode* b, TreeNode* c, TreeNode* T0, TreeNode* T1, TreeNode* T2, TreeNode* T3)
	{
		a->parent = b; a->lc = T0; a->rc = T1;
		c->parent = b; c->lc = T2; c->rc = T3;
		b->lc = a; b->rc = c;
		T0->parent = T1->parent = a;
		T2->parent = T3->parent = c;
		updateHeight(a);
		updateHeight(c);
		updateHeight(b);		
	}

	bool isBalance(TreeNode* node)
	{
		int balanceFactor = node->lc->h - node->rc->h;
		return -2 < balanceFactor && balanceFactor < 2;
	}

	void updateHeight(TreeNode* node)
	{
		if (node->lc->h > node->rc->h)
		{
			node->h = node->lc->h + 1;
		}
		else
		{
			node->h = node->rc->h + 1;
		}
	}

	TreeNode* higherChild(TreeNode* node)
	{
		return node->lc->h > node->rc->h ? node->lc : node->rc;
	}

	void postOrderFree(TreeNode* node)
	{
		if (node != nullNode)
		{
			if (node->lc != nullNode)
				postOrderFree(node->lc);
			if (node->rc != nullNode)
				postOrderFree(node->rc);
			delete node;
		}
	}

	template<TreeNode* TreeNode::* p1, TreeNode* TreeNode::* p2>
	TreeNode* neighbour(TreeNode* node)
	{
		TreeNode* ret;
		if (node->*p1 != nullNode)
		{
			ret = node->*p1;
			while (ret->*p2 != nullNode)
			{
				ret = ret->*p2;
			}
			return ret;
		}
		ret = node;
		while (ret->parent != nullNode && ret->parent->*p1 == ret)
		{
			ret = ret->parent;
		}
		return ret->parent != nullNode ? ret->parent : nullptr;
	}	

public:
	AVLTree()
	{
		if (!nullNode)
		{
			nullNode = new TreeNode(Key{}, 0);
		}
		root = nullNode;
	}

	~AVLTree()
	{
		postOrderFree(root);
	}

	TreeNode* predecessor(TreeNode* node)
	{
		return neighbour<&TreeNode::lc, &TreeNode::rc>(node);
	}

	TreeNode* successor(TreeNode* node)
	{
		return neighbour<&TreeNode::rc, &TreeNode::lc>(node);
	}

	TreeNode* lowerBound(const Key& k)		//different from std::lower_bound in semantics; return the greatest element whose key is no greater than 'k', if not found, return nullptr
	{
		TreeNode* node = find(k);
		if (comp(k, node->k))
		{
			return predecessor(node);
		}
		return node;
	}

	TreeNode* first()
	{
		TreeNode* ret = root;
		while (ret->lc != nullNode)
		{
			ret = ret->lc;
		}
		return ret;
	}

	TreeNode* last()
	{
		TreeNode* ret = root;
		while (ret->rc != nullNode)
		{
			ret = ret->rc;
		}
		return ret;
	}

	TreeNode* find(const Key& k)		//if not found, return the last node visited
	{
		TreeNode* cursor = root;
		TreeNode* last = cursor;
		while (cursor != nullNode)
		{
			last = cursor;
			if (comp(cursor->k, k))
			{
				cursor = cursor->rc;
			}
			else if (comp(k, cursor->k))
			{
				cursor = cursor->lc;
			}
			else
			{
				return cursor;
			}
		}
		return last;
	}

	void insert(const Key& k)
	{
		TreeNode* cur = new TreeNode(k, 1);
		if (root == nullNode)
		{
			root = cur;
			return;
		}

		TreeNode* p = find(k);

		cur->parent = p;
		if (comp(k, p->k))
		{
			p->lc = cur;
		}
		else
		{
			p->rc = cur;
		}
		updateHeight(p);
		TreeNode* gp = p->parent;
		while (gp != nullNode)
		{
			if (!isBalance(gp))
			{
				rebalance(cur, p, gp);
				return;
			}
			updateHeight(gp);
			cur = p;
			p = gp;
			gp = gp->parent;
		}
	}

	void removeByKey(const Key& k)
	{
		removeByPtr(find(k));
	}

	void removeByPtr(TreeNode* node)
	{
		TreeNode *gp;
		if (node->lc != nullNode && node->rc != nullNode)
		{
			TreeNode* succ = successor(node);
			if (root == node)
			{
				root = succ;
			}
			if (succ->parent == node)
			{
				succ->lc = node->lc;
				node->lc->parent = succ;
				succ->parent = node->parent;
				if (node == node->parent->lc)
				{
					node->parent->lc = succ;
				}
				else
				{
					node->parent->rc = succ;
				}
				gp = succ;
			}
			else
			{
				gp = succ->parent;
				if (node == node->parent->lc)
				{
					node->parent->lc = succ;
				}
				else
				{
					node->parent->rc = succ;
				}
				node->lc->parent = succ;
				node->rc->parent = succ;

				succ->rc->parent = succ->parent;
				succ->parent->lc = succ->rc;

				succ->lc = node->lc;
				succ->rc = node->rc;
				succ->parent = node->parent;
					
			}

			delete node;
		}
		else if (node->lc != nullNode)
		{
			if (node == root)
			{
				root = node->lc;
				root->parent = nullNode;
				gp = nullNode;
			}
			else
			{
				node->lc->parent = node->parent;
				if (node->parent->lc == node)
				{
					node->parent->lc = node->lc;
				}
				else
				{
					node->parent->rc = node->lc;
				}
				gp = node->parent;
			}
			delete node;
		}
		else
		{
			if (node == root)
			{
				root = node->rc;
				root->parent = nullNode;
				gp = nullNode;
			}
			else
			{
				node->rc->parent = node->parent;
				if (node->parent->lc == node)
				{
					node->parent->lc = node->rc;
				}
				else
				{
					node->parent->rc = node->rc;
				}
				gp = node->parent;
			}
			delete node;
		}

		while (gp != nullNode)
		{
			if (!isBalance(gp))
			{
				TreeNode* p = higherChild(gp);
				gp = rebalance(higherChild(p), p, gp)->parent;
			}
			else
			{
				updateHeight(gp);
				gp = gp->parent;
			}
		}
	}

#ifdef DEBUG
	bool isTreeBalance()
	{
		return root == nullNode || isSubTreeBalance(root);
	}

	bool isSubTreeBalance(TreeNode* node)
	{
		return node == nullNode || isBalance(node->lc) && isBalance(node->rc);
	}

	int inOrderTraversal(vector<Key>& outVec, TreeNode* node)
	{
		int h = 0;
		if (node->lc != nullNode)
		{
			h = inOrderTraversal(outVec, node->lc);
		}
		outVec.emplace_back(node->k);
		if (node->rc != nullNode)
		{
			h = std::max(h, inOrderTraversal(outVec, node->rc));
		}
		return h + 1;
	}

	int serialize(vector<Key>& outVec)
	{
		return inOrderTraversal(outVec, root);
	}
#endif // DEBUG

};

template<typename Key, typename Comp>
typename AVLTree<Key,Comp>::TreeNode* AVLTree<Key, Comp>::nullNode = nullptr;

template<typename Key, typename Comp = std::less<Key>>
using BST = AVLTree<Key, Comp>;

template<typename Key, typename Comp = std::less<Key>>
using BSTNode = typename BST<Key, Comp>::TreeNode;



class DynamicConvexHull
{
	struct UpperHullComp
	{
		bool operator()(const Point& lhs, const Point& rhs) const
		{
			return lhs.x < rhs.x || lhs.x == rhs.x && lhs.y < rhs.y;
		}
	};

	struct LowerHullComp
	{
		bool operator()(const Point& lhs, const Point& rhs) const
		{
			return lhs.x > rhs.x || lhs.x == rhs.x && lhs.y > rhs.y;
		}
	};
	BST<Point, UpperHullComp> upperHull;
	BST<Point, LowerHullComp> lowerHull;

	template<typename Comp, typename T = typename std::enable_if<std::is_same<Comp, UpperHullComp>::value>::type>
	BST<Point, UpperHullComp>& getHull()
	{
		return upperHull;
	}

	template<typename Comp, typename T = typename std::enable_if<std::is_same<Comp, LowerHullComp>::value>::type>
	BST<Point, LowerHullComp>& getHull()
	{
		return lowerHull;
	}

	template<typename Comp>
	struct HullCache
	{
		BSTNode<Point, Comp>* last, *lb, *lbSucc;
	};

	HullCache<UpperHullComp> upperHullCache;
	HullCache<LowerHullComp> lowerHullCache;


	template<typename Comp, typename T = typename std::enable_if<std::is_same<Comp, UpperHullComp>::value>::type>
	HullCache<UpperHullComp>& getHullCache()
	{
		return upperHullCache;
	}

	template<typename Comp, typename T = typename std::enable_if<std::is_same<Comp, LowerHullComp>::value>::type>
	HullCache<LowerHullComp>& getHullCache()
	{
		return lowerHullCache;
	}

	template<typename Comp>
	bool query(const Point& p)
	{
		using SNode = BSTNode<Point, Comp>;
		BST<Point, Comp>& hull = getHull<Comp>();
		HullCache<Comp>& hullCache = getHullCache<Comp>();
		hullCache.lb = hull.lowerBound(p);
		hullCache.last = hull.last();
		if (hullCache.lb)
		{
			if (hullCache.lb != hullCache.last)
			{
				hullCache.lbSucc = hull.successor(hullCache.lb);
				return (p - hullCache.lb->k).cross(hullCache.lbSucc->k - hullCache.lb->k) >= 0;
			}
			else
			{
				return p == hullCache.last->k;
			}
		}
		return false;
	}

	template<typename Comp1, typename Comp2>
	void handleInfiniteSlab(const Point& p)
	{
		BST<Point, Comp1>& hull1 = getHull<Comp1>();
		BSTNode<Point, Comp1>* current1 = hull1.first();
		BSTNode<Point, Comp1>* next1 = hull1.successor(current1);
		while (next1)
		{
			if ((current1->k - p).cross(next1->k - p) >= 0)
			{
				hull1.removeByPtr(current1);
				current1 = next1;
				next1 = hull1.successor(current1);
			}
			else
			{
				break;
			}
		}
		hull1.insert(p);

		BST<Point, Comp2>& hull2 = getHull<Comp2>();
		BSTNode<Point, Comp2>* current2 = getHullCache<Comp2>().last;
		BSTNode<Point, Comp2>* next2 = hull2.predecessor(current2);
		while (next2)
		{
			if ((current2->k - p).cross(next2->k - p) <= 0)
			{
				hull2.removeByPtr(current2);
				current2 = next2;
				next2 = hull2.predecessor(current2);
			}
			else
			{
				break;
			}
		}
		hull2.insert(p);
	}

	template<typename Comp>
	void handleFiniteSlab(const Point& p)
	{
		BST<Point, Comp>& hull = getHull<Comp>();
		HullCache<Comp>& hullCache = getHullCache<Comp>();
		BSTNode<Point, Comp> *curr, *pred, *succ;
		curr = hullCache.lbSucc;
		succ = hull.successor(curr);
		while (succ)
		{
			if ((curr->k - p).cross(succ->k - p) >= 0)
			{
				hull.removeByPtr(curr);
				curr = succ;
				succ = hull.successor(curr);
			}
			else
			{
				break;
			}
		}

		curr = hullCache.lb;
		pred = hull.predecessor(curr);
		while (pred)
		{
			if ((curr->k - p).cross(pred->k - p) <= 0)
			{
				hull.removeByPtr(curr);
				curr = pred;
				pred = hull.predecessor(curr);
			}
			else
			{
				break;
			}
		}

		hull.insert(p);
	}

public:
	DynamicConvexHull(const Point& p1, const Point& p2)
	{
		upperHull.insert(p1);
		upperHull.insert(p2);
		lowerHull.insert(p1);
		lowerHull.insert(p2);
	}

	bool inConvexHullQuery(const Point& p)
	{
		return query<UpperHullComp>(p) && query<LowerHullComp>(p);
	}

	void insert(const Point& p)
	{
		bool insideUpper, insideLower;
		insideUpper = query<UpperHullComp>(p);
		insideLower = query<LowerHullComp>(p);
		if (!(insideLower && insideUpper))
		{
			if (!upperHullCache.lb)			//left infinite slab
			{
				handleInfiniteSlab<UpperHullComp, LowerHullComp>(p);
			}
			else if (!lowerHullCache.lb)		//right infinite slab
			{
				handleInfiniteSlab<LowerHullComp, UpperHullComp>(p);
			}
			else if (insideLower)		//insert to upperHull
			{
				handleFiniteSlab<UpperHullComp>(p);
			}
			else						//insert to lowerHull
			{
				handleFiniteSlab<LowerHullComp>(p);
			}
		}
	}
};

#ifdef DEBUG
bool testCorrectness(int nAll, int nDel = 0)		//check if the tree is correct after doing #nAll insertions and #nDel deletions
{
	std::set<int> set;
	std::vector<int> insertVec;
	insertVec.reserve(nAll);
	std::vector<int> ansVec;
	ansVec.reserve(nAll);
	std::vector<int> splayVec;
	splayVec.reserve(nAll);
	std::vector<int> delVec(nAll, 0);
	std::vector<int> maskVec(nAll, 0);

	std::default_random_engine e;
	std::uniform_int_distribution<int> u(0, nAll - 1);
	std::uniform_int_distribution<int> u100(1, 100);

	int testNeighbourAccess = 0;

	BST<int> myBST;

	//calculate random deletion points
	int pos = 0;
	for (int i = 0; i < nDel; ++i)
	{
		do
		{
			pos = (pos + e()) % nAll;
		} while (delVec[pos]);
		delVec[pos] = 1;
	}

	for (int i = 1; i <= nAll; ++i)
	{
		insertVec.emplace_back(i);
	}
	std::shuffle(insertVec.begin(), insertVec.end(), e);

	for (int i = 0; i < nAll; ++i)
	{
		if (delVec[i])
		{
			std::uniform_int_distribution<int> distribution(0, i);
			int id;
			while (id = distribution(e), maskVec[id]);
			delVec[i] = insertVec[id];
			maskVec[id] = 1;
		}
	}
	for (int i = 0; i < nAll; ++i)
	{
		//insert
		int insertVal = insertVec[i];
		set.emplace(insertVal);
		myBST.insert(insertVal);

		//delete
		if (delVec[i])
		{
			set.erase(delVec[i]);
			myBST.removeByKey(delVec[i]);
		}

	}

	for (auto t : set)
	{
		ansVec.emplace_back(t);
	}
	cout << myBST.serialize(splayVec) << endl;
	cout << "Test Neighbour Access: " << testNeighbourAccess << std::endl;

	if (splayVec != ansVec)
	{
		cout << "Incorrect tree structure!\n";
		return false;
	}
	if (std::is_same_v<decltype(myBST), AVLTree<int>>)
	{
		if (!reinterpret_cast<AVLTree<int>*>(&myBST)->isTreeBalance())
		{
			cout << "AVL Tree is not balanced!\n";
			return false;
		}
	}

	return true;
}

void testPerformance(int nAll, int nDel = 0)
{
	set<int> set;
	vector<int> insertVec;
	std::vector<int> delVec(nAll, 0);
	std::vector<int> maskVec(nAll, 0);

	std::default_random_engine e;
	std::uniform_int_distribution<int> u(0, nAll - 1);
	for (int i = 1; i <= nAll; ++i)
	{
		insertVec.emplace_back(i);
	}
	std::shuffle(insertVec.begin(), insertVec.end(), e);

	int pos = 0;
	for (int i = 0; i < nDel; ++i)
	{
		do
		{
			pos = (pos + e()) % nAll;
		} while (delVec[pos]);
		delVec[pos] = 1;
	}

	for (int i = 0; i < nAll; ++i)
	{
		if (delVec[i])
		{
			std::uniform_int_distribution<int> distribution(0, i);
			int id;
			while (id = distribution(e), maskVec[id]);
			delVec[i] = insertVec[id];
			maskVec[id] = 1;
		}
	}

	clock_t start = clock();
	for (int i = 0; i < nAll; ++i)
	{
		set.insert(insertVec[i]);
		if (delVec[i])
		{
			set.erase(delVec[i]);
		}
	}
	clock_t end = clock();
	cout << "Time used by std::set: " << static_cast<double>(end - start) / CLOCKS_PER_SEC << std::endl;

	start = clock();
	BST<int> myBST;

	for (int i = 0; i < nAll; ++i)
	{
		myBST.insert(insertVec[i]);
		if (delVec[i])
		{
			myBST.removeByKey(delVec[i]);
		}
	}
	end = clock();
	cout << "Time used by my BST: " << static_cast<double>(end - start) / CLOCKS_PER_SEC << std::endl;
}

void random_point(int& x, int &y)
{
	static std::uniform_int_distribution<int> u(-1e6, 1e6);
	static std::default_random_engine e;
	x = u(e);
	y = u(e);
}

struct Rational
{
	int denominator, numerator;
	Rational(int d, int n) :denominator(d), numerator(n) {}
	bool operator<(const Rational& r) const
	{
		return static_cast<long long int>(numerator) * r.denominator < static_cast<long long int>(denominator) * r.numerator;
	}
};

int sortRational(int k, set<Rational>& outVec)
{
	outVec.emplace(1, 1);
	for (int i = 2; i <= k; ++i)
	{
		for (int j = 1; j < i; ++j)
		{
			if (std::gcd(i, j) == 1)
			{
				outVec.emplace(j, i);
				outVec.emplace(i, j);
			}
		}
	}
	int range = 0;
	for (auto& r : outVec)
	{
		range += r.denominator;
	}
	assert(range < 1000000000);
	return outVec.size();
}

void generateToughCase(int k)
{
	std::ofstream file("toughcase.txt");
	set<Rational> s;
	int n = 4 * sortRational(k, s) + 2;
	int start = -1e9;
	int end = 1e9;
	int h1 = 0, h2 = 0;
	auto f = [&file](int a, int b) {file << 1 << ' ' << a << ' ' << b << '\n'; };
	file << n << '\n';
	f(start, 0);
	f(end, 0);
	int tx = start, ty = 0;
	vector<std::pair<int, int>> vec;
	for (auto& r : s)
	{
		tx += r.numerator;
		ty += r.denominator;
		vec.emplace_back(tx, ty);
		vec.emplace_back(-tx, -ty);
		vec.emplace_back(tx, -ty);
		vec.emplace_back(-tx, ty);
	}
	std::shuffle(vec.begin(), vec.end(), std::default_random_engine());
	for (auto& p : vec)
	{
		f(p.first, p.second);
	}

	file.close();
}
#endif




int main()
{
	setvbuf(stdin, new char[1 << 20], _IOFBF, 1 << 20);
	setvbuf(stdout, new char[1 << 20], _IOFBF, 1 << 20);

	int n;
#ifdef DEBUG
	freopen("toughcase.txt", "r", stdin);
	clock_t start, end;
	start = clock();
#endif // DEBUG

	scanf("%d", &n);
	int cmd, x, y;
	scanf("%d%d%d", &cmd, &x, &y);
	Point p1(x, y);
	scanf("%d%d%d", &cmd, &x, &y);
	Point p2(x, y);
	DynamicConvexHull DCH(p1, p2);
	for (int i = 2; i < n; ++i)
	{
		scanf("%d%d%d", &cmd, &x, &y);
		if (cmd == 1)
		{
			DCH.insert(Point(x, y));
		}
		else
		{
			if (DCH.inConvexHullQuery(Point(x, y)))
			{
				printf("YES\n");
			}
			else
			{
				printf("NO\n");
			}
		}
	}
#ifdef DEBUG
	end = clock();
	cout << static_cast<double>(end - start) / CLOCKS_PER_SEC << std::endl;
#endif // DEBUG


	return 0;
}
