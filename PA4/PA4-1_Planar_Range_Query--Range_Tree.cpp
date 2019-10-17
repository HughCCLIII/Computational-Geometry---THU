/**
 *

	2D range tree to solve 2D "number of points in axis-aligned rectangular area" query
	Time: O(nlogn) for preprocessing, O(logn) for single query
	Space:O(nlogn)


	注意的问题和实现细节：
	1.在第一层对值val进行查找时，在树中查找的是不小于val的最小节点（因此需要一个右哨兵），在一般的BST中执行此类的查找还需要分情况讨论，但在这里借助于我们在树的叶子节点保存了所有节点的拷贝，我们只需要一直深入搜索到叶子节点即可。在每个内部节点处，向右深入当且仅当查找目标值严格大于内部节点的值。由于我们查找的是不小于val的最小节点，很自然我们可以舍弃右边的叶子节点，包含左边的叶子节点，从而根据查询算法的流程得到一个左闭右开的区间

	  第二层的查找区间左闭右开 ylist有右哨兵保证迭代器不会到end

 */

#include<iostream>
#include<memory>
#include<vector>
#include<algorithm>

using namespace std;

using CoordType = long long int;

const CoordType INF = 1000003;

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
		return this->x < other.x || this->x == other.x && this->y < other.y;
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

struct RangeTree2D
{
	struct XNode;
	struct YNode;

	struct XNode
	{
		Point p;
		unique_ptr<XNode> lc, rc;
		vector<YNode> ylist;

		XNode(const Point& _p) :p(_p)			//for initialization of leaf node
		{
			ylist.emplace_back(_p);
			ylist.emplace_back(Point(INF, INF));
		}

		XNode(const Point& _p, XNode* _lc, XNode* _rc) :p(_p), lc(_lc), rc(_rc)
		{
			auto leftIt = _lc->ylist.cbegin(), rightIt = _rc->ylist.cbegin();
			int sz = _lc->ylist.size() + _rc->ylist.size() - 2;
			for (int i = 0; i < sz; ++i)
			{
				if (*leftIt < *rightIt)
				{
					ylist.emplace_back(leftIt->p, leftIt, rightIt);
					++leftIt;
				}
				else
				{
					ylist.emplace_back(rightIt->p, leftIt, rightIt);
					++rightIt;
				}
			}
			ylist.emplace_back(leftIt->p, leftIt, rightIt);
		}
	};

	struct YNode
	{
		Point p;
		vector<YNode>::const_iterator lcIter, rcIter;

		YNode(const Point& _p) :p(_p) {}
		YNode(const Point& _p, vector<YNode>::const_iterator _lcIter, vector<YNode>::const_iterator _rcIter)
			:p(_p), lcIter(_lcIter), rcIter(_rcIter) {}
		YNode(Point&& _p) :p(move(_p)) {}

		bool operator<(const YNode& rhs) const
		{
			return p.y < rhs.p.y || (p.y == rhs.p.y && p.x < rhs.p.x);
		}

		bool operator==(const YNode& rhs) const
		{
			return p == rhs.p;
		}
	};

	unique_ptr<XNode> searchRoot;

	pair<Point, XNode*> merge(const pair<Point, XNode*>& p1, const pair<Point, XNode*>& p2)
	{
		return make_pair(p2.first, new XNode(p1.first, p1.second, p2.second));
	}

	RangeTree2D(vector<Point>& _vp)
	{

		vector<pair<Point, XNode*>> curLevel, nextLevel;
		vector<pair<Point, XNode*>>* curLevelPtr = &curLevel, *nextLevelPtr = &nextLevel;

		_vp.emplace_back(INF - 1, INF - 1);		//left sentinel
		sort(_vp.begin(), _vp.end());
		for (const Point& p : _vp)
		{
			curLevel.emplace_back(p, new XNode(p));
		}


		while (curLevelPtr->size() > 1)
		{
			auto it = curLevelPtr->cbegin();
			if (curLevelPtr->size() % 2 == 0)
			{
				for (; it != curLevelPtr->cend(); it += 2)
				{
					nextLevelPtr->emplace_back(merge(*it, *(it + 1)));
				}
			}
			else
			{
				for (; it != curLevelPtr->cend() - 1; it += 2)
				{
					nextLevelPtr->emplace_back(merge(*it, *(it + 1)));
				}
				nextLevelPtr->emplace_back(*it);

			}

			curLevelPtr->clear();
			swap(curLevelPtr, nextLevelPtr);
		}
		searchRoot.reset(curLevelPtr->cbegin()->second);
	}

	int query(CoordType xl, CoordType xh, CoordType yl, CoordType yh)
	{
		using namespace std::rel_ops;

		Point xLB(xl, -INF), xUB(xh, INF);
		YNode yLB(Point(-INF, yl)), yUB(Point(INF, yh));
		XNode* LCA = searchRoot.get();
		while (LCA->lc)
		{
			if (xLB > LCA->p && xUB > LCA->p)
			{
				LCA = LCA->rc.get();
			}
			else if(xLB <= LCA->p && xUB <= LCA->p)
			{
				LCA = LCA->lc.get();
			}
			else
			{
				break;
			}
		}
		if (!LCA->lc)
		{
			return 0;
		}
		XNode *leftCursor = LCA->lc.get(), *rightCursor = LCA->rc.get();
		vector<YNode>::const_iterator leftLo, leftHi, rightLo, rightHi;
		leftLo = rightLo = lower_bound(LCA->ylist.cbegin(), LCA->ylist.cend(), yLB);
		leftHi = rightHi = lower_bound(LCA->ylist.cbegin(), LCA->ylist.cend(), yUB);

		leftLo = leftLo->lcIter;
		leftHi = leftHi->lcIter;
		rightLo = rightLo->rcIter;
		rightHi = rightHi->rcIter;

		int res = 0;
		while (leftCursor->lc)
		{
			if (xLB > leftCursor->p)
			{
				leftCursor = leftCursor->rc.get();
				leftHi = leftHi->rcIter;
				leftLo = leftLo->rcIter;
			}
			else
			{
				res += leftHi->rcIter - leftLo->rcIter;
				leftCursor = leftCursor->lc.get();
				leftHi = leftHi->lcIter;
				leftLo = leftLo->lcIter;
			}
		}

		res += leftHi - leftLo;

		while (rightCursor->lc)
		{
			if (xUB > rightCursor->p)
			{
				res += rightHi->lcIter - rightLo->lcIter;
				rightCursor = rightCursor->rc.get();
				rightHi = rightHi->rcIter;
				rightLo = rightLo->rcIter;
			}
			else
			{
				rightCursor = rightCursor->lc.get();
				rightHi = rightHi->lcIter;
				rightLo = rightLo->lcIter;
			}
		}
		return res;
	}
};

int main()
{
	int nPoints, nQueries;
	cin >> nPoints >> nQueries;
	CoordType x1, y1, x2, y2;
	vector<Point> vp;
	for (int i = 0; i < nPoints; ++i)
	{
		cin >> x1 >> y1;
		vp.emplace_back(x1, y1);
	}
	RangeTree2D RT(vp);
	for (int i = 0; i < nQueries; ++i)
	{
		cin >> x1 >> y1 >> x2 >> y2;
		cout << RT.query(x1, x2, y1, y2) << "\n";
	}

	return 0;
}