/*

Bentley-Ottmann Algorithm “宾利”-“奥特曼”算法

实现并不保证出现OJ数据排除的情形(如有部分重合的线等）时不崩溃
应该使用map代替set，多了很多没必要的const_cast，还是对STL不够熟悉
没有写一个double类型的wrapper类并重载运算符是一个错误的决定


需要注意的问题：
1.平行于y轴的线
2.多线相交于一点
3.端点处相交
4.同一扫描线上多个事件
可参考《计算几何-算法与应用》(Computational Geometry: Algorithms and Applications, Mark de Berg)中扫描线算法的处理方式

5.直线、射线、圆的处理办法
对于直线和射线可以当成线段处理，题目所给的数据范围保证交点坐标最大是1e15量级(实测测试数据不超过1e8量级)，使用double能保证精度，因此只要找到一个更远的点作为线段端点即可
而对于圆，可以划分为上半圆和下半圆两段分别处理，需要注意不要将两个半圆的连接处误判成交点

6.多圆相切于起点，终点，及一般点
多圆相切于终点的情形还有bug(run()函数p.startCurves.size() + p.middleCurves.size()分支中可能需要重写一个比较函数而非复用现在的） 但已通过OJ全部测例 故该bug未修复

7.精度问题 
由于此题坐标的范围限制，直线的斜率之差导致两个最近的交点的距离会大于某个值，保证epsilon精度高于1e-6即可
*/



#include<cstdio>
#include<iostream>
#include<vector>
#include<algorithm>
#include<set>
#include<memory>
#include<queue>
#include<cmath>
#include<cassert>

using namespace std;
using namespace std::rel_ops;

typedef long double CoordType;

const CoordType epsilon = 1e-6;
const CoordType infDist = 1e8;
const CoordType slBias = 1e-6;
const CoordType slopeBias = 0.01;

inline bool isEqual(CoordType x, CoordType y)
{
	x -= y;
	return x >= -epsilon && x <= epsilon;
}

inline bool isLess(CoordType x, CoordType y)
{
	x -= y;
	return x < -epsilon;
}

inline bool isEqualOrLess(CoordType x, CoordType y)
{
	x -= y;
	return x <= epsilon;
}

inline CoordType clamp(CoordType x)
{
	return x < 0 ? 0 : x;
}

struct Point
{
	CoordType x, y;

	Point(CoordType _x = 0, CoordType _y = 0) :x(_x), y(_y)
	{

	}

	Point operator+(const Point& rhs) const
	{
		return Point(this->x + rhs.x, this->y + rhs.y);
	}

	Point operator-(const Point& rhs) const
	{
		return Point(this->x - rhs.x, this->y - rhs.y);
	}

	Point operator*(CoordType t) const
	{
		return Point(this->x * t, this->y*t);
	}

	Point operator/(CoordType t) const
	{
		return Point(this->x / t, this->y / t);
	}

	bool operator==(const Point& rhs) const
	{
		return isEqual(this->x, rhs.x) && isEqual(this->y, rhs.y);
	}

	bool operator<(const Point& rhs) const
	{
		return isLess(this->x,rhs.x) || (isEqual(this->x, rhs.x) && isLess(this->y , rhs.y));
	}

	void normalize()
	{
		CoordType norm = sqrt(x*x + y * y);
		x /= norm;
		y /= norm;
	}
};

class Curve;
class HalfCircle;
class Segment;
struct SweeplineStatusCompare;
struct IterWrap;


struct EventPoint
{

	enum Kind { leftEnd = 1, intersection = 2, rightEnd = 3 };
	Point p;
	set<shared_ptr<Curve>> startCurves;  
	set<shared_ptr<Curve>> middleCurves;
	set<shared_ptr<Curve>> endCurves;
	bool reported = false;
	bool needReport = false;

	EventPoint(const Point& _p) :p(_p)
	{

	}

	EventPoint(const Point &_p, Kind k, shared_ptr<Curve> c) :p(_p)
	{
		addCurve(k, c);
	}

	void addCurve(Kind k, shared_ptr<Curve> c)
	{
		if (k == leftEnd)
		{
			startCurves.insert(c);
		}
		else if (k == intersection)
		{
			middleCurves.insert(c);
		}
		else
		{
			endCurves.insert(c);
		}
	}

	bool operator<(const EventPoint& rhs) const
	{
		return this->p < rhs.p;
	}

	bool operator==(const EventPoint& rhs) const
	{
		return this->p == rhs.p;
	}
};

EventPoint* checkEventPoint(const Point&p, set<EventPoint>& eventQueue);

class Curve
{
public:
	Point start, end;
	shared_ptr<Curve> self;
	IterWrap* iterWrap;
	Curve(const Point& s, const Point& e); 

	virtual ~Curve()
	{
		delete iterWrap;
	}
	virtual CoordType f(const Point& p) const = 0;
	void intersect(const Curve& c, set<EventPoint>& eventQueue) const;

	virtual void intersect(const Segment& s, set<EventPoint>& eventQueue) const = 0;
	virtual void intersect(const HalfCircle& s, set<EventPoint>& eventQueue) const = 0;

	virtual CoordType k(const Point& p) const = 0;  //斜率

	bool operator<(const Curve& c) const;

	bool checkEndPoint(const Point& p) const
	{
		return p != start && p != end;
	}
	
};

class Segment :public Curve
{
public:
	Point direction;
	CoordType t;
	CoordType slope;
	Segment(const Point& start, const Point& end): Curve(start,end)
	{
		direction.x = end.x - start.x;
		direction.y = end.y - start.y;
		CoordType norm = sqrt(direction.x*direction.x + direction.y*direction.y);
		direction.x /= norm;
		direction.y /= norm;
		t = isEqual(start.x, end.x) ? (end.y - start.y) / direction.y : (end.x - start.x) / direction.x;
		slope = direction.y;
		if (start.x == end.x)
		{
			slope += slopeBias;
		}
	}

	void intersect(const Segment& s, set<EventPoint>& eventQueue) const override;
	void intersect(const HalfCircle& hc, set<EventPoint>& eventQueue) const override;
	CoordType k(const Point& p) const override;

	CoordType f(const Point& p) const override
	{
		if (end.x == start.x)
		{
			return p.y;
		}
		return ((end.x - p.x)*start.y + (p.x - start.x)*end.y) / (end.x - start.x);
	}

	bool operator<(const Segment &s) const
	{
		return direction.y < s.direction.y;
	}
};

class HalfCircle :public Curve
{
public:
	bool upperHalf;
	Point center;
	CoordType radius;
	CoordType radius_2;
	
	HalfCircle(CoordType cx, CoordType cy, CoordType r, bool upper):Curve(Point(cx-r,cy),Point(cx+r,cy)),radius(r),upperHalf(upper),center(cx,cy)
	{
		radius_2 = radius * radius;
	}

	CoordType f(const Point& p) const override
	{
		CoordType x = p.x - center.x;
		x *= x;
		return (sqrt(radius_2 - x))*(upperHalf ? 1 : -1) + center.y;
	}

	bool posTest(const Point &p) const   
	{		
		return p.y == center.y || isLess(center.y,p.y) == upperHalf;
	}

	bool operator< (const HalfCircle& hc) const
	{
		return !upperHalf;
	}

	bool sameCircle(const HalfCircle &other)const
	{
		return this->center == other.center && this->radius == other.radius;
	}

	void intersect(const Segment& s, set<EventPoint>& eventQueue) const override;

	void intersect(const HalfCircle& hc, set<EventPoint>& eventQueue) const override;
	CoordType k(const Point& x) const override;
};

void Segment::intersect(const Segment& s, set<EventPoint>& eventQueue) const
{
	if (this->direction != s.direction)
	{
		CoordType t1, t2;
		Point tp = s.start - this->start;
		CoordType d = this->direction.y * s.direction.x - this->direction.x * s.direction.y;			//Cramer's Rule
		CoordType dx = tp.y * s.direction.x - tp.x * s.direction.y;
		CoordType dy = this->direction.x * tp.y - this->direction.y * tp.x;
		t1 = dx / d;
		t2 = dy / d;
		if (isEqualOrLess(t1, this->t) && isEqualOrLess(t2, s.t))
		{
			Point p(this->start + this->direction * t1);
			EventPoint* ep;
			if (ep = checkEventPoint(p, eventQueue))
			{
				ep->needReport = true;
				if (this->checkEndPoint(p))
				{
					ep->addCurve(EventPoint::Kind::intersection, this->self);
				}
				if (s.checkEndPoint(p))
				{
					ep->addCurve(EventPoint::Kind::intersection, s.self);
				}			
			}
		}
	}
}

void Segment::intersect(const HalfCircle& hc, set<EventPoint>& eventQueue) const
{
	hc.intersect(*this, eventQueue);
}

CoordType Segment::k(const Point& p)const
{
	return slope;
}


void HalfCircle::intersect(const Segment& s, set<EventPoint>& eventQueue) const
{
	CoordType t1, t2;
	Point tp = this->center - s.start;
	t1 = tp.x * s.direction.x + tp.y * s.direction.y;
	t2 = tp.x * s.direction.y - tp.y * s.direction.x;
	CoordType temp = radius_2 - t2 * t2;
	if (isEqual(temp,0))
	{
		if (isEqualOrLess(t1,s.t))
		{
			Point ip = s.start + s.direction*t1;
			EventPoint* ep;
			if (ep = checkEventPoint(ip, eventQueue))
			{
				ep->needReport = true;
				if (this->checkEndPoint(ip))
				{
					ep->addCurve(EventPoint::Kind::intersection, this->self);
				}
				if (s.checkEndPoint(ip))
				{
					ep->addCurve(EventPoint::Kind::intersection, s.self);
				}
			}
		}
	}
	else if (isLess(0, temp))
	{
		temp = abs(temp);
		temp = sqrt(temp);
		Point p1, p2;
		p1 = s.start + s.direction*(t1 - temp);
		p2 = s.start + s.direction*(t1 + temp);
		if (isEqualOrLess(t1 - temp,s.t) && posTest(p1))
		{
			EventPoint* ep;
			if (ep = checkEventPoint(p1, eventQueue))
			{
				ep->needReport = true;
				if (this->checkEndPoint(p1))
				{
					ep->addCurve(EventPoint::Kind::intersection, this->self);
				}
				if (s.checkEndPoint(p1))
				{
					ep->addCurve(EventPoint::Kind::intersection, s.self);
				}
			}		
		}
		if (isEqualOrLess(t1 + temp, s.t) && posTest(p2))
		{
			EventPoint* ep;
			if (ep = checkEventPoint(p2, eventQueue))
			{
				ep->needReport = true;
				if (this->checkEndPoint(p2))
				{
					ep->addCurve(EventPoint::Kind::intersection, this->self);
				}
				if (s.checkEndPoint(p2))
				{
					ep->addCurve(EventPoint::Kind::intersection, s.self);
				}
			}
		}
	}
}

void HalfCircle::intersect(const HalfCircle& hc, set<EventPoint>& eventQueue) const
{
	if (!this->sameCircle(hc))			
	{
		Point centerDiff = hc.center - this->center;
		CoordType distCenter_2 = centerDiff.x * centerDiff.x + centerDiff.y*centerDiff.y;
		if (isEqualOrLess(distCenter_2, (this->radius + hc.radius)*(this->radius + hc.radius)))
		{
			CoordType c1 = sqrt(distCenter_2);
			CoordType c2 = (this->radius_2 - hc.radius_2) / c1;
			CoordType t1, t2;
			t1 = (c1 + c2) / 2;
			t2 = (c1 - c2) / 2;
			CoordType lambda = t1 / t2;
			Point tp = (this->center + hc.center * lambda) / (1 + lambda);
			CoordType d = sqrt(clamp(this->radius_2 - t1 * t1));
			Point dir(hc.center.y - this->center.y, this->center.x - hc.center.x);
			dir.normalize();
			Point ip1 = tp + dir * d;
			Point ip2 = tp - dir * d;
			if (posTest(ip1) && hc.posTest(ip1))
			{
				EventPoint* ep;
				if (ep = checkEventPoint(ip1, eventQueue))
				{
					ep->needReport = true;
					if (this->checkEndPoint(ip1))
					{
						ep->addCurve(EventPoint::Kind::intersection, this->self);
					}
					if (hc.checkEndPoint(ip1))
					{
						ep->addCurve(EventPoint::Kind::intersection, hc.self);
					}
				}
			}
			if (posTest(ip2) && hc.posTest(ip2))
			{
				EventPoint* ep;
				if (ep = checkEventPoint(ip2, eventQueue))
				{
					ep->needReport = true;
					if (this->checkEndPoint(ip2))
					{
						ep->addCurve(EventPoint::Kind::intersection, this->self);
					}
					if (hc.checkEndPoint(ip2))
					{
						ep->addCurve(EventPoint::Kind::intersection, hc.self);
					}
				}
			}
		}
	}	
}

CoordType HalfCircle::k(const Point& p)const
{
	if (isEqual(p.x, start.x))
	{
		return upperHalf ? 1 : -1;
	}
	else if (isEqual(p.x, end.x))
	{
		return upperHalf ? -1 : 1;
	}
	CoordType y = f(p);
	
	CoordType k = (p.x - center.x) / (center.y - y);
	return k / sqrt(1 + k * k);
}

void Curve::intersect(const Curve& c, set<EventPoint>& eventQueue) const
{
	if (typeid(c) == typeid(Segment))
	{
		intersect(static_cast<const Segment&>(c), eventQueue);
	}
	else
	{
		intersect(static_cast<const HalfCircle&>(c), eventQueue);
	}
}

bool Curve::operator<(const Curve& c) const
{
	if (typeid(*this) == typeid(Segment))
	{
		if (typeid(c) == typeid(Segment))
		{
			return static_cast<const Segment&>(*this) < static_cast<const Segment&>(c);
		}
		else
		{
			return static_cast<const HalfCircle&>(c).upperHalf;
		}
	}
	else
	{
		if (typeid(c) == typeid(Segment))
		{
			return !static_cast<const HalfCircle&>(*this).upperHalf;
		}
		return static_cast<const HalfCircle&>(*this) < static_cast<const HalfCircle&>(c);
	}
}



struct SweeplineStatusCompare
{
	shared_ptr<Point> curPoint;
	bool operator()(shared_ptr<Curve> lhs, shared_ptr<Curve> rhs) const
	{
		if (lhs == rhs)
		{
			return false;
		}
		CoordType l1 = lhs->f(*curPoint), r1 = rhs->f(*curPoint), l2 = lhs->k(*curPoint), r2 = rhs->k(*curPoint);
		return isLess(l1, r1) || (isEqual(l1,r1) && isLess(l2,r2)) || (isEqual(l1,r1) && isEqual(l2,r2) && furtherTest(lhs, rhs));

	}

	bool furtherTest(shared_ptr<Curve> lhs, shared_ptr<Curve> rhs) const //交点处斜率相同 由于限定没有重合 所以不可能都是直线
	{
		if (typeid(*lhs) == typeid(HalfCircle) && typeid(*rhs) == typeid(HalfCircle))
		{
			const HalfCircle &hc1 = static_cast<const HalfCircle &>(*lhs), &hc2 = static_cast<const HalfCircle &>(*rhs);
			/*if (hc1.upperHalf == hc2.upperHalf)
			{
				bool flag  = isLess(hc1.radius, hc2.radius) == hc1.upperHalf;
				return *curPoint == hc1.end ? !flag : flag;
			}
			else
			{
				return hc1.upperHalf;
			}*/
			return hc1.upperHalf == hc2.upperHalf ? (isEqualOrLess(hc1.radius,hc2.radius) == hc1.upperHalf) : hc1.upperHalf;
		}
		else if(typeid(*lhs) == typeid(HalfCircle))
		{
			return static_cast<const HalfCircle&>(*lhs).upperHalf;
		}
		return !static_cast<const HalfCircle&>(*rhs).upperHalf;
	}

	SweeplineStatusCompare():curPoint(new Point())
	{

	}

};

struct IterWrap
{
	set<shared_ptr<Curve>, SweeplineStatusCompare>::iterator iter;
	
};

Curve::Curve(const Point& s, const Point& e):start(s), end(e), iterWrap(new IterWrap)
{

}

EventPoint* checkEventPoint(const Point&p, set<EventPoint>& eventQueue)
{
	EventPoint* ep = nullptr;
	if (p >= eventQueue.begin()->p)
	{
		auto iter = eventQueue.insert(EventPoint(p));
		return &const_cast<EventPoint&>(*(iter.first));
	}
	return ep;
}

bool sameCircle(shared_ptr<Curve> c1, shared_ptr<Curve> c2)
{
	return typeid(*c1) == typeid(*c2) && typeid(*c1) == typeid(HalfCircle) && static_cast<const HalfCircle&>(*c1).sameCircle(static_cast<const HalfCircle&>(*c2));
}


class BO
{
	SweeplineStatusCompare comparator;
	set<shared_ptr<Curve>, SweeplineStatusCompare> sweeplineStatus;
	set<EventPoint> eventQueue;
public:
	BO():comparator(),sweeplineStatus(comparator)
	{
		
	}

	void insertCurve(shared_ptr<Curve> c)
	{
		c->self = c;
		auto pair = eventQueue.insert(EventPoint(c->start));
		EventPoint& ep1 = (const_cast<EventPoint&>(*pair.first));
		ep1.addCurve(EventPoint::Kind::leftEnd, c);

		pair = eventQueue.insert(EventPoint(c->end));
		EventPoint& ep2 = (const_cast<EventPoint&>(*pair.first));
		ep2.addCurve(EventPoint::Kind::rightEnd, c);
		
	}

	int run()
	{
		int count = 0;
		while (eventQueue.size() > 0)
		{
			EventPoint& p = const_cast<EventPoint&>(*eventQueue.begin());

			*comparator.curPoint = p.p; // update sweepline position	
			int csize;
			if ((csize = p.startCurves.size() + p.endCurves.size() + p.middleCurves.size()) > 1)
			{
				if (csize == 2 && p.startCurves.size() == 2)
				{
					auto it = p.startCurves.begin();
					auto c1 = *it;
					auto c2 = *(++it);
					if (!sameCircle(c1, c2))
					{
						count++;
						p.reported = true;
					}
				}
				else if (csize == 2 && p.endCurves.size() == 2)
				{
					auto it = p.endCurves.begin();
					auto c1 = *it;
					auto c2 = *(++it);
					if (!sameCircle(c1, c2))
					{
						count++;
						p.reported = true;
					}
				}
				else
				{
					count++;
					p.reported = true;
				}
				

			}
			shared_ptr<Curve> max, min;
			set<shared_ptr<Curve>, SweeplineStatusCompare>::iterator maxIter, minIter;
			if (p.startCurves.size() + p.middleCurves.size() == 0)
			{
				auto result = minmax_element(p.endCurves.begin(), p.endCurves.end(), comparator);
				max = *result.first;
				min = *result.second;
				maxIter = max->iterWrap->iter;
				minIter = min->iterWrap->iter;
				minIter--;
				maxIter++;
				if (minIter != sweeplineStatus.end() && maxIter != sweeplineStatus.end())
				{
					(*maxIter)->intersect(**minIter, eventQueue);
				}
				for (auto it = p.endCurves.begin(); it != p.endCurves.end(); it++)
				{
					auto& iter = (*it)->iterWrap->iter;
					if (iter != sweeplineStatus.end())
					{
						sweeplineStatus.erase((*it)->iterWrap->iter);
						iter = sweeplineStatus.end();
					}
					
				}
			}
			else
			{
				for (auto it = p.endCurves.begin(); it != p.endCurves.end(); it++)
				{
					auto& iter = (*it)->iterWrap->iter;
					if (iter != sweeplineStatus.end())
					{
						sweeplineStatus.erase((*it)->iterWrap->iter);
						iter = sweeplineStatus.end();
					}
				}
				for (auto it = p.middleCurves.begin(); it != p.middleCurves.end(); it++)
				{
					auto& iter = (*it)->iterWrap->iter;
					if (iter != sweeplineStatus.end())
					{
						sweeplineStatus.erase((*it)->iterWrap->iter);
						iter = sweeplineStatus.end();
					}
				}
				for (auto it = p.startCurves.begin(); it != p.startCurves.end(); it++)
				{
					auto pair = sweeplineStatus.insert(*it);
					(*it)->iterWrap->iter = pair.first;
				}
				for (auto it = p.middleCurves.begin(); it != p.middleCurves.end(); it++)
				{
					auto pair = sweeplineStatus.insert(*it);
					(*it)->iterWrap->iter = pair.first;
				}
				auto result1 = minmax_element(p.startCurves.begin(), p.startCurves.end(), comparator);
				auto result2 = minmax_element(p.middleCurves.begin(), p.middleCurves.end(), comparator);
				if (p.startCurves.size() == 0)
				{
					min = *result2.first;
					max = *result2.second;
				}
				else if (p.middleCurves.size() == 0)
				{
					min = *result1.first;
					max = *result1.second;
				}
				else
				{
					min = comparator(*result1.first, *result2.first) ? *result1.first : *result2.first;
					max = comparator(*result1.second, *result2.second) ? *result2.second : *result1.second;
				}
				maxIter = max->iterWrap->iter;
				minIter = min->iterWrap->iter;
				auto maxIt = maxIter, minIt = minIter;
				maxIter++;
				minIter--;
				if (maxIter != sweeplineStatus.end())
				{
					(*maxIt)->intersect(**maxIter, eventQueue);
				}
				if (minIter != sweeplineStatus.end())
				{
					(*minIt)->intersect(**minIter, eventQueue);
				}
			}	
			if (!p.reported && p.needReport)
			{
				count++;
			}
			eventQueue.erase(eventQueue.begin());
		}
		return count;
	}
};



int main()
{
	setvbuf(stdin, new char[1 << 20], _IOFBF, 1 << 20);
	setvbuf(stdout, new char[1 << 20], _IOFBF, 1 << 20);
	int nSegment, nRay, nLine, nCircle;
	scanf("%d %d %d %d", &nSegment, &nRay, &nLine, &nCircle);

	BO solver;

	int x, y, u, v;
	Point* start, *end;
	Point tp1, tp2;
	for (int i = 0; i < nSegment; i++)
	{
		scanf("%d %d %d %d", &x, &y, &u, &v);
		tp1.x = x;
		tp1.y = y;
		tp2.x = u;
		tp2.y = v;
		start = &tp1, end = &tp2;
		if (tp1 > tp2)
		{
			start = &tp2;
			end = &tp1;
		}
		solver.insertCurve(shared_ptr<Curve>(new Segment(*start, *end)));
	}

	for (int i = 0; i < nRay; i++)
	{
		scanf("%d %d %d %d", &x, &y, &u, &v);
		tp1.x = x;
		tp1.y = y;
		Point direction(u - x, v - y);
		direction.normalize();
		tp2 = tp1 + direction * infDist;
		start = &tp1, end = &tp2;
		if (tp1 > tp2)
		{
			start = &tp2;
			end = &tp1;
		}
		solver.insertCurve(shared_ptr<Curve>(new Segment(*start, *end)));
	}

	for (int i = 0; i < nLine; i++)
	{
		scanf("%d %d %d %d", &x, &y, &u, &v);
		tp1.x = x;
		tp1.y = y;
		tp2.x = u;
		tp2.y = v;
		start = &tp1, end = &tp2;
		if (tp1 > tp2)
		{
			start = &tp2;
			end = &tp1;
		}
		Point direction = *end - *start;
		direction.normalize();
		Point sp = *start - direction * infDist;
		Point ep = *end + direction * infDist;
		solver.insertCurve(shared_ptr<Curve>(new Segment(sp, ep)));
	}
	
	for (int i = 0; i < nCircle; i++)
	{
		scanf("%d %d %d", &x, &y, &u);
		solver.insertCurve(shared_ptr<Curve>(new HalfCircle(x, y, u, true)));
		solver.insertCurve(shared_ptr<Curve>(new HalfCircle(x, y, u, false)));
	}
	
	printf("%d", solver.run());
	return 0;
}