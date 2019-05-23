/*

Jarvis March Algorithm

需要注意的问题：
1. int32的溢出
2. 多点共线

*/


#include<vector>
#include<cstdio>

using namespace std;

struct Point
{
	int x, y;
	bool marked;

	Point(int _x, int _y) :x(_x), y(_y), marked(false)
	{

	}
};

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

void JarvisMarch(vector<Point>& points, vector<int>& edgePoints)
{
	vector<Point>::iterator ltl = points.begin();
	for (auto it = ltl + 1; it != points.end(); it++)
	{
		if (it->y < ltl->y || (it->y == ltl->y && it->x < ltl->x))
		{
			ltl = it;
		}
	}


	vector<Point>::iterator curStart = ltl;
	vector<Point>::iterator curEnd;
	vector<Point>::iterator cursor;
	vector<int> candidates;  
	bool finished = false;
	while (!finished)
	{
		for (cursor = points.begin(); cursor->marked || cursor == curStart; cursor++);
		candidates.emplace_back(cursor - points.begin() + 1);
		curEnd = cursor;
		for (cursor++; cursor != points.end(); cursor++)
		{
			if (!cursor->marked && cursor != curStart)
			{
				long long int tlTestRes = toLeftTest(*curStart, *curEnd, *cursor);
				if (tlTestRes < 0)
				{
					curEnd = cursor;
					candidates.clear();
					candidates.emplace_back(curEnd - points.begin() + 1);
				}
				else if (tlTestRes == 0)
				{
					candidates.emplace_back(cursor - points.begin() + 1);
					if (!between(*curStart, *curEnd, *cursor))  //此时必然处于延长线上而非反向延长线上，由凸包性质和初始ltl选点保证。 
					{
						curEnd = cursor;
					}
				}
			}
		}
		finished = curEnd == ltl;
		curStart = curEnd;
		edgePoints.insert(edgePoints.end(), candidates.begin(), candidates.end());
		for (auto it = candidates.begin(); it != candidates.end(); it++)
		{
			points[*it-1].marked = true;
		}
		candidates.clear();

	}

}

int main()
{
	setvbuf(stdin, new char[1 << 20], _IOFBF, 1 << 20);
	setvbuf(stdout, new char[1 << 20], _IOFBF, 1 << 20);
	int n;
	scanf("%d", &n);
	vector<Point> points;
	vector<int> edgePoints;
	int tx, ty;
	for (int i = 0; i < n; i++) 
	{
		scanf("%d %d", &tx, &ty);
		points.emplace_back(tx, ty);
	}

	JarvisMarch(points, edgePoints);
	long long int res = 1;
	edgePoints.emplace_back(edgePoints.size());
	for (auto it = edgePoints.begin(); it != edgePoints.end(); it++)
	{
		res *= *it;
		res %= (n + 1);
	}
	printf("%lld", res);
	return 0;
}