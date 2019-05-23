/*

Graham Scan Algorithm

需要注意的问题
1. int32的溢出
2. 使用leftmost then lowest方法选定初始点后作为极角排序的基准点后，排序构成可能出现极角相同的点，为了保证
算法的正确性，我使用的处理方式是将认为较远的点极角更小（我认为这个处理方法是正确的）。但在第一条极边上出现共线时，
这种处理方法会有问题，需要特别对待。

*/


#include<cstdio>
#include<vector>
#include<memory>
#include<algorithm>

using namespace std;

struct Point
{
	static int cnt;
	int x, y;
	int number;
	Point(int _x, int _y):x(_x),y(_y),number(cnt++)
	{

	}

	bool operator==(const Point& rhs)
	{
		return this->number == rhs.number;
	}
};

int Point::cnt = 1;

long long int toLeftTest(const Point& start, const Point& end, const Point& testpoint)  // positive-left negative-right zero-on the line
{
	long long int ax = end.x - start.x;
	long long int ay = end.y - start.y;
	long long int bx = testpoint.x - start.x;
	long long int by = testpoint.y - start.y;
	ax *= by;
	ay *= bx;
	ax -= ay;
	return ax;
}

bool between(const Point& start, const Point& end, const Point& testpoint)
{
	long long int tx1 = start.x - testpoint.x, tx2 = end.x - testpoint.x, ty1 = start.y - testpoint.y, ty2 = end.y - testpoint.y;
	tx1 *= tx2;
	ty1 *= ty2;
	return tx1 <= 0 && ty1 <= 0;
}

struct PointCompare
{
	const shared_ptr<Point> ltl;

	PointCompare(const shared_ptr<Point> _ltl) :ltl(_ltl)
	{

	}

	bool operator()(const shared_ptr<Point> lhs, const shared_ptr<Point> rhs)
	{
		long long int res = toLeftTest(*ltl, *lhs, *rhs);
		return res != 0 ? res < 0 : !between(*ltl, *lhs, *rhs);
	}
};


void grahamScan(vector<shared_ptr<Point>>& points, vector<shared_ptr<Point>>& convexHull)
{
	vector<shared_ptr<Point>>::iterator ltl = points.begin();
	for (auto it = points.begin()+1; it != points.end(); it++)
	{
		if ((*it)->y < (*ltl)->y || ((*it)->y == (*ltl)->y && (*it)->x < (*ltl)->x))
		{
			ltl = it;
		}
	}
	shared_ptr<Point> pltl = *ltl;
	convexHull.emplace_back(*ltl);
	PointCompare comparator(*ltl);
	points.erase(ltl);

	sort(points.begin(), points.end(), comparator);		//共线时认为较远的点极角较小
	convexHull.emplace_back(points.back());
	points.pop_back();

	shared_ptr<Point> curStart, curEnd, curTest;
	long long int testRes;
	while (points.size() > 0)
	{
		curEnd = convexHull.back();
		curStart = *(convexHull.end() - 2);
		curTest = points.back();
		if ((testRes=toLeftTest(*curStart, *curEnd, *curTest)) >= 0)
		{
			if (testRes == 0 && *curStart == *pltl)		//第一条极边共线情况的特判
			{
				convexHull.insert(convexHull.end() - 2, curTest);
			}
			else
			{
				convexHull.emplace_back(curTest);
			}
			points.pop_back();
		}
		else
		{
			convexHull.pop_back();
		}
	}
}

int main()
{
	setvbuf(stdin, new char[1 << 20], _IOFBF, 1 << 20);
	setvbuf(stdout, new char[1 << 20], _IOFBF, 1 << 20);
	int n;
	scanf("%d", &n);
	int tx, ty;
	vector<shared_ptr<Point>> points;
	vector<shared_ptr<Point>> convexHull;
	for (int i = 0; i < n; i++)
	{
		scanf("%d %d", &tx, &ty);
		points.emplace_back(new Point(tx, ty));
	}

	grahamScan(points, convexHull);
	long long int res = convexHull.size();
	for (auto it = convexHull.begin(); it != convexHull.end(); it++)
	{
		res *= (*it)->number;
		res %= (n + 1);
	}
	printf("%lld", res);
	return 0;
}