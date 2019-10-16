/**
 *

 Solve point location problem using Trapezoidal Map(Time: expected-O(nlogn) for preprocessing, expected-O(logn) for a single query; Space: expected-O(n))

 ��Ҫע��������һЩʵ��ϸ�ڣ�

 1. �㷨��ϣ������������ͬ�ĵ�����ͬһ��ֱ���ϵ���������������Զ����е㰲��һ���ֵ���x������ͬ�ĵ�Ƚ�y���꣩���������ǽ�һ����ֱ���߿�������΢��������б�����������������Ҳ�������Ϊ�����е�����һ����С���б�任��ʹ��û������������ͬ��x���꣩

 2. �������������߶������غϵ���������Ȼ��Щ�غϵ�������߶εĶ˵㣬����������һ��subdivisionΪ����ʱ��Ȼ����ֵ����Ρ�ʵ�ֿ����˵��غ����ε�δ���Թ���OJû����Ӧ������

 3. ����ѯ�����ض��߶λ��ض����غ�ʱ����α�����:
		i. ����OJҪ��Ĳ��ң����ݱȽϺ����Ķ��壬���ص����ε����Ҷ˵�left,right�͵�ǰ�ڵ���ֵ������� left<p<=right����p�ĺ������right�����ʱ������top�߶Σ� ���ʱ�����к�right�������߶�
		ii. ���ڲ����߶���˵�Ĳ��ң���������غϵ㣬��ôӦ�ü������Ҳ��ң�������������߶��ϵ��������Ҫ�Ƚ��߶�б����ȷ������������

 4. ��������ʵ�ֵĲ�ѯ�ṹ�У�ÿ�����λᱣ���������ϡ����¡����ϡ������ĸ������ھӵ����ã�һ����λ��������ĸ�����û�У�һ����λ��ͨ��1�Ĵ��������Ա�֤��������top�ߵ�Ϊ�Ϸ��ھӣ����һ�����������ھӵ������ھ�����������Щ�ھӵ�ֵֻȷ�����ڵ��ھ���ȷ��ֵ�������ڵ��ھӲ���֤�ǿ�ָ�롣�ڲ�ѯ������߶��ཻ������ʱ�����ȸ��ݲ����߶���˵��ҵ����������Σ�Ȼ��ͨ�����������ô��������ҵ�һϵ�����Ρ�
	�ڴ�����Щ����ʱ��������������������м����Щ���Σ����߶ε�һ���ֹᴩ��ǰ���Ρ���ǰ���α�����Ϊ���������µ����Σ�����һ��������ߵ�һ������������������Ҫͨ����ǰ������˵���߶ε����¹�ϵȷ������˵㲻�������߶��ϣ���Ϊ�߶��м䲻�����������߶��ཻ����

5. OJƽֻ̨֧��c++11���ʽ�c++17��д����c++11(std::variant-->union),ע��unionû��ʵ��������������memory leak
 */

#include<iostream>
#include<algorithm>
#include<vector>
#include<list>
#include<memory>
#include<random>
#include<cassert>

using namespace std;

using CoordType = long long int;

struct Point
{
	CoordType x, y;
	int id;
	Point(CoordType _x = 0, CoordType _y = 0, int _id = 0) :id(_id), x(_x), y(_y)
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

struct Segment
{
	Point left, right;
	Segment(const Point& p1, const Point& p2) :left(p1), right(p2)
	{

	}

	CoordType toLeft(const Point& p) const
	{
		return (right - left).cross(p - left);
	}
};

struct SearchNode;
struct TrapezoidNode;
using SNPtr = shared_ptr<SearchNode>;
using SNPPtr = shared_ptr<SNPtr>;

struct PointData
{
	Point p;
	PointData(const Point& _p) :p(_p){}
};
struct SegmentData
{
	Segment s;
	SegmentData(const Segment& _s) :s(_s) {}
};
struct TrapezoidData
{
	Segment top, bottom;
	Point left, right;
	SNPPtr upperRight, upperLeft, lowerRight, lowerLeft;
	TrapezoidData(const Point& _left, const Point& _right, const Segment& _top, const Segment& _bottom) :left(_left), right(_right), top(_top), bottom(_bottom) {}
};
using VData = union U{ 
	PointData pd; SegmentData sd; TrapezoidData td; 
	U(PointData&& _pd) :pd(move(_pd)) {}
	U(SegmentData&& _sd) :sd(move(_sd)) {}
	U(TrapezoidData&& _td) :td(move(_td)) {}
	~U() {}		//memory leak here
};


struct SearchNode
{
	SNPPtr lc, rc;
	VData data;					
	SearchNode(PointData&& _pd, SNPPtr _lc = SNPPtr(), SNPPtr _rc = SNPPtr()) :data(move(_pd)), lc(_lc), rc(_rc)
	{

	}
	SearchNode(SegmentData&& _sd, SNPPtr _lc = SNPPtr(), SNPPtr _rc = SNPPtr()) :data(move(_sd)), lc(_lc), rc(_rc)
	{

	}
	SearchNode(TrapezoidData&& _td, SNPPtr _lc = SNPPtr(), SNPPtr _rc = SNPPtr()) :data(move(_td)), lc(_lc), rc(_rc)
	{

	}

	virtual bool visitLeft(const Point& tp) const = 0;		//for query of the on-line judge problem use, true means we should visit the left child
	virtual bool visitLeft(const Segment& ts) const = 0;		//for insertSegment() use, true means we should visit the left child
	virtual bool isTerminal() const {
		return false;
	}
	virtual ~SearchNode() = default;
};

struct PointNode :public SearchNode
{
	PointNode(const Point& _p, SNPPtr _lc = SNPPtr(), SNPPtr _rc = SNPPtr()) :SearchNode(PointData(_p), _lc, _rc)
	{

	}

	bool visitLeft(const Point& tp) const override
	{
		auto& pData = data.pd;
		return tp < pData.p || (tp == pData.p);
	}

	bool visitLeft(const Segment& ts) const override
	{
		return ts.left < data.pd.p;
	}
};

struct SegmentNode :public SearchNode
{
	SegmentNode(const Segment& _s, SNPPtr _lc = SNPPtr(), SNPPtr _rc = SNPPtr()) :SearchNode(SegmentData(_s), _lc, _rc)
	{

	}

	bool visitLeft(const Point& tp) const override
	{
		auto& s = data.sd.s;
		return s.toLeft(tp) > 0;
	}

	bool visitLeft(const Segment& ts) const override
	{
		auto& s = data.sd.s;
		auto leftCross = s.toLeft(ts.left);
		return leftCross > 0 || (leftCross == 0 && s.toLeft(ts.right) > 0);
	}
};

struct TrapezoidNode :public SearchNode
{
	TrapezoidNode(const Point& _left, const Point& _right, const Segment& _top, const Segment& _bottom, SNPPtr _lc = SNPPtr(), SNPPtr _rc = SNPPtr()) :
		SearchNode(TrapezoidData(_left, _right, _top, _bottom), _lc, _rc)
	{

	}

	bool visitLeft(const Point& tp) const override
	{
		assert(false);
		return false;
	}

	bool visitLeft(const Segment& ts) const override
	{
		assert(false);
		return false;
	}

	bool isTerminal() const override
	{
		return true;
	}
};

struct TrapezoidalMap
{
	SNPPtr searchRoot;

	TrapezoidalMap()
	{
		//construct the boundary trapezoid
		const CoordType INF = 1000003;
		Point p1(-INF, INF), p2(INF, -INF), p3(INF, INF), p4(-INF, -INF);
		searchRoot = make_shared<SNPtr>(make_shared<TrapezoidNode>(p1, p2, Segment(p1, p3), Segment(p2, p4)));
		auto neighbourSentry = make_shared<SNPtr>(make_shared<TrapezoidNode>(p1, p1, Segment(p1, p1), Segment(p1, p1)));
		setTopNeighbour(searchRoot, neighbourSentry);
		setBottomNeighbour(searchRoot, neighbourSentry);
		setTopNeighbour(neighbourSentry, searchRoot);
		setBottomNeighbour(neighbourSentry, searchRoot);
	}

	void setBottomNeighbour(SNPPtr& left, SNPPtr& right)
	{
		left->get()->data.td.lowerRight = right;
		right->get()->data.td.lowerLeft = left;
	}

	void setTopNeighbour(SNPPtr& left, SNPPtr& right)
	{
		left->get()->data.td.upperRight = right;
		right->get()->data.td.upperLeft = left;
	}

	void rightBorderNeighbourhoodCheck(TrapezoidData& trapezoid, SNPPtr& top, SNPPtr& bottom)
	{
		if (trapezoid.top.toLeft(trapezoid.right) != 0)
		{
			setTopNeighbour(top, trapezoid.upperRight);
		}
		if (trapezoid.bottom.toLeft(trapezoid.right) != 0)
		{
			setBottomNeighbour(bottom, trapezoid.lowerRight);
		}
	}

	void leftBorderNeighbourhoodCheck(TrapezoidData& trapezoid, SNPPtr& top, SNPPtr& bottom)
	{
		if (trapezoid.top.toLeft(trapezoid.left) != 0)
		{
			setTopNeighbour(trapezoid.upperLeft, top);
		}
		if (trapezoid.bottom.toLeft(trapezoid.left) != 0)
		{
			setBottomNeighbour(trapezoid.lowerLeft, bottom);
		}
	}

	void insertSegment(const Segment& s)
	{
		using namespace std::rel_ops;

		SNPtr* curTreeNode = query(s);
		SNPtr* nextTreeNode;

		TrapezoidData* curTrapezoid = &curTreeNode->get()->data.td;

		SNPPtr lastTop, lastBottom;	//��һ�����α��зֳɵ���������

		//�����һ������
		if (s.right > curTrapezoid->right)	//����һ��
		{
			lastTop = make_shared<SNPtr>(make_shared<TrapezoidNode>(s.left, curTrapezoid->right, curTrapezoid->top, s));
			lastBottom = make_shared<SNPtr>(make_shared<TrapezoidNode>(s.left, curTrapezoid->right, s, curTrapezoid->bottom));
			rightBorderNeighbourhoodCheck(*curTrapezoid, lastTop, lastBottom);
			if (s.toLeft(curTrapezoid->right) > 0)
			{
				nextTreeNode = curTrapezoid->lowerRight.get();
			}
			else
			{
				nextTreeNode = curTrapezoid->upperRight.get();
			}
			if (s.left == curTrapezoid->left)
			{
				leftBorderNeighbourhoodCheck(*curTrapezoid, lastTop, lastBottom);
				curTreeNode->reset(new SegmentNode(s, lastTop, lastBottom));
			}
			else
			{
				SNPPtr leftTrapezoid = make_shared<SNPtr>(make_shared<TrapezoidNode>(curTrapezoid->left, s.left, curTrapezoid->top, curTrapezoid->bottom));
				leftBorderNeighbourhoodCheck(*curTrapezoid, leftTrapezoid, leftTrapezoid);
				setTopNeighbour(leftTrapezoid, lastTop);
				setBottomNeighbour(leftTrapezoid, lastBottom);
				curTreeNode->reset(new PointNode(s.left, leftTrapezoid, make_shared<SNPtr>(make_shared<SegmentNode>(s, lastTop, lastBottom))));
			}

			curTreeNode = nextTreeNode;
			curTrapezoid = &curTreeNode->get()->data.td;

			//�м䲿��
			while (s.right > curTrapezoid->right)
			{
				if (s.toLeft(curTrapezoid->left) > 0)	//������˵��ڲ����߶��Ϸ�����ô�������������
				{
					SNPPtr upperTrapezoid = make_shared<SNPtr>(make_shared<TrapezoidNode>(curTrapezoid->left, curTrapezoid->right, curTrapezoid->top, s));
					lastBottom->get()->data.td.right = curTrapezoid->right;
					leftBorderNeighbourhoodCheck(*curTrapezoid, upperTrapezoid, upperTrapezoid);
					setBottomNeighbour(lastTop, upperTrapezoid);
					lastTop = upperTrapezoid;
				}
				else
				{
					SNPPtr lowerTrapezoid = make_shared<SNPtr>(make_shared<TrapezoidNode>(curTrapezoid->left, curTrapezoid->right, s, curTrapezoid->bottom));
					lastTop->get()->data.td.right = curTrapezoid->right;
					leftBorderNeighbourhoodCheck(*curTrapezoid, lowerTrapezoid, lowerTrapezoid);
					setTopNeighbour(lastBottom, lowerTrapezoid);
					lastBottom = lowerTrapezoid;
				}

				rightBorderNeighbourhoodCheck(*curTrapezoid, lastTop, lastBottom);
				if (s.toLeft(curTrapezoid->right) > 0)	//�����Ҷ˵��ڲ����߶��Ϸ�����һ���������ھ�
				{
					nextTreeNode = curTrapezoid->lowerRight.get();
				}
				else
				{
					nextTreeNode = curTrapezoid->upperRight.get();
				}
				curTreeNode->reset(new SegmentNode(s, lastTop, lastBottom));
				curTreeNode = nextTreeNode;
				curTrapezoid = &curTreeNode->get()->data.td;
			}
			//���һ������
			if (s.toLeft(curTrapezoid->left) > 0)
			{
				SNPPtr upperTrapezoid = make_shared<SNPtr>(make_shared<TrapezoidNode>(curTrapezoid->left, s.right, curTrapezoid->top, s));
				lastBottom->get()->data.td.right = s.right;
				leftBorderNeighbourhoodCheck(*curTrapezoid, upperTrapezoid, upperTrapezoid);
				setBottomNeighbour(lastTop, upperTrapezoid);
				lastTop = upperTrapezoid;
			}
			else
			{
				SNPPtr lowerTrapezoid = make_shared<SNPtr>(make_shared<TrapezoidNode>(curTrapezoid->left, s.right, s, curTrapezoid->bottom));
				lastTop->get()->data.td.right = s.right;
				leftBorderNeighbourhoodCheck(*curTrapezoid, lowerTrapezoid, lowerTrapezoid);
				setTopNeighbour(lastBottom, lowerTrapezoid);
				lastBottom = lowerTrapezoid;
			}

			if (s.right == curTrapezoid->right)
			{
				rightBorderNeighbourhoodCheck(*curTrapezoid, lastTop, lastBottom);
				curTreeNode->reset(new SegmentNode(s, lastTop, lastBottom));
			}
			else
			{
				SNPPtr rightTrapezoidNode = make_shared<SNPtr>(make_shared<TrapezoidNode>(s.right, curTrapezoid->right, curTrapezoid->top, curTrapezoid->bottom));
				setTopNeighbour(lastTop, rightTrapezoidNode);
				setBottomNeighbour(lastBottom, rightTrapezoidNode);
				rightBorderNeighbourhoodCheck(*curTrapezoid, rightTrapezoidNode, rightTrapezoidNode);
				SNPPtr segmentNode = make_shared<SNPtr>(make_shared<SegmentNode>(s, lastTop, lastBottom));
				curTreeNode->reset(new PointNode(s.right, segmentNode, rightTrapezoidNode));
			}
		}
		else
		{
			lastTop = make_shared<SNPtr>(make_shared<TrapezoidNode>(s.left, s.right, curTrapezoid->top, s));
			lastBottom = make_shared<SNPtr>(make_shared<TrapezoidNode>(s.left, s.right, s, curTrapezoid->bottom));

			SearchNode* tempNode;
			if (s.left == curTrapezoid->left)
			{
				leftBorderNeighbourhoodCheck(*curTrapezoid, lastTop, lastBottom);
				tempNode = new SegmentNode(s, lastTop, lastBottom);
			}
			else
			{
				SNPPtr leftTrapezoid = make_shared<SNPtr>(make_shared<TrapezoidNode>(curTrapezoid->left, s.left, curTrapezoid->top, curTrapezoid->bottom));
				leftBorderNeighbourhoodCheck(*curTrapezoid, leftTrapezoid, leftTrapezoid);
				setTopNeighbour(leftTrapezoid, lastTop);
				setBottomNeighbour(leftTrapezoid, lastBottom);
				tempNode = new PointNode(s.left, leftTrapezoid, make_shared<SNPtr>(make_shared<SegmentNode>(s, lastTop, lastBottom)));
			}

			if (s.right == curTrapezoid->right)
			{
				rightBorderNeighbourhoodCheck(*curTrapezoid, lastTop, lastBottom);
				curTreeNode->reset(tempNode);
			}
			else
			{
				SNPPtr rightTrapezoid = make_shared<SNPtr>(make_shared<TrapezoidNode>(s.right, curTrapezoid->right, curTrapezoid->top, curTrapezoid->bottom));
				rightBorderNeighbourhoodCheck(*curTrapezoid, rightTrapezoid, rightTrapezoid);
				setTopNeighbour(lastTop, rightTrapezoid);
				setBottomNeighbour(lastBottom, rightTrapezoid);
				curTreeNode->reset(new PointNode(s.right, make_shared<SNPtr>(tempNode), rightTrapezoid));
			}
		}



	}

	template<typename T>
	SNPtr* query(const T& elem)
	{
		auto cursor = searchRoot.get();
		while (!cursor->get()->isTerminal())
		{
			cursor = cursor->get()->visitLeft(elem) ? cursor->get()->lc.get() : cursor->get()->rc.get();
		}
		return cursor;
	}

};



int main()
{
	int n, m, id;
	cin >> n >> m;

	Point p1, p2;

	TrapezoidalMap TM;

	vector<Segment> segVec;

	for (int i = 1; i <= n; ++i)
	{
		cin >> p1.x >> p1.y >> p2.x >> p2.y;
		p1.id = p2.id = i;
		if (p2 < p1)
		{
			swap(p1, p2);
		}
		segVec.emplace_back(p1, p2);
		shuffle(segVec.begin(), segVec.end(), default_random_engine());
	}
	for (auto& s : segVec)
	{
		TM.insertSegment(s);
	}

	for (int i = 1; i <= m; ++i)
	{
		cin >> p1.x >> p1.y;
		TrapezoidData& res = TM.query(p1)->get()->data.td;
		if (res.right.x == p1.x)
		{
			id = res.right.id;
		}
		else
		{
			id = res.top.left.id;
		}
		if (id > 0)
		{
			cout << id << "\n";
		}
		else
		{
			cout << "N\n";
		}
	}
	return 0;
}