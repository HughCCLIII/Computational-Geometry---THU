/*

Construct Voronoi Diagram wih DCEL representation using Fortune's sweepline algorithm(O(nlogn))
then construct the slab decomposition data structure from DCEL in O(nlogn) time(if we exclude the time of memory allcoation and copy) and do point location query in O(logn) time
use persistent tree structure can reduce the storage space of the slab decomposition data structure from O(n^2) to O(n), which is not implemented in my code

需要注意的问题（主要是Voronoi图的构造）
Voronoi Diagram:
1. 增加边界时，要剔除边界外的顶点以及“相关联的边”
2. 当两个site处于同一水平线上时的情况
3. 浮点数精度问题影响很大，一些认为是理论上严格大于的判断由于误差的存在可能需要改为大于等于，最后通过测例有一定运气成分（对于自己随机生成的测例由于精度不够容易崩溃）
4. 有一种退化情况在代码中没有处理，则Site Event的事件点，正好处于断点下方时

Slab Decomposition:
1. 对于水平边的处理（可以视为一条斜率极小的向左上倾斜的边）
*/


#include<cstdio>
#include<vector>
#include<map>
#include<queue>
#include<algorithm>
#include<memory>
#include<set>
#include<cmath>
#include<cassert>
#include<iostream>
#include<fstream>
#include<list>
#include<limits>
#include<random>



using namespace std;
using namespace std::rel_ops;


const double PINF = 3e5;
const double NINF = -3e5;

struct CoordType
{
	static const double epsilon;
	double coord;

	CoordType(double d = 0) :coord(d)
	{

	}

	const CoordType& operator=(const CoordType& other)
	{
		coord = other.coord;
		return *this;
	}

	CoordType operator+(const CoordType& other) const
	{
		return CoordType(coord + other.coord);
	}

	CoordType operator-(const CoordType& other) const
	{
		return CoordType(coord - other.coord);
	}

	CoordType operator*(const CoordType& other) const
	{
		return CoordType(coord * other.coord);
	}

	CoordType operator/(const CoordType& other) const
	{
		return CoordType(coord / other.coord);
	}

	CoordType& operator+=(const CoordType& other)
	{
		coord += other.coord;
		return *this;
	}

	CoordType& operator-=(const CoordType& other)
	{
		coord -= other.coord;
		return *this;
	}

	CoordType& operator*=(const CoordType& other)
	{
		coord *= other.coord;
		return *this;
	}

	CoordType& operator/=(const CoordType& other)
	{
		coord /= other.coord;
		return *this;
	}

	CoordType operator-() const
	{
		return CoordType(-coord);
	}

	CoordType operator+() const
	{
		return CoordType(coord);
	}

	bool operator==(const CoordType& other) const
	{
		double diff = coord - other.coord;
		return diff >= -epsilon && diff <= epsilon;
	}

	bool operator<(const CoordType& other) const
	{
		return coord - other.coord < -epsilon;
	}
};

CoordType sqrt(const CoordType& c)
{
	return CoordType(sqrt(c.coord > 0 ? c.coord : 0));
}

const double CoordType::epsilon = 1e-6;

CoordType COORD_PINF(PINF);
CoordType COORD_NINF(NINF);

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

	void normalize()
	{
		double norm = sqrt(x.coord * x.coord + y.coord * y.coord);
		x.coord /= norm;
		y.coord /= norm;
	}

	CoordType dot(const Point& other) const
	{
		return x * other.x + y * other.y;
	}
	CoordType cross(const Point& other) const
	{
		return x * other.y - y * other.x;
	}

	CoordType norm() const
	{
		return sqrt(x * x + y * y);
	}

};

Point POINT_INF(COORD_PINF, COORD_PINF);

bool isFinite(const Point& p)
{
	return p.x < COORD_PINF && p.x > COORD_NINF && p.y > COORD_NINF && p.y < COORD_PINF;
}

Point intersect(const Point&p1, const Point&d1, const Point&p2, const Point&d2)
{
	Point ip = POINT_INF;
	if (d1 != d2 && d1 != -d2)
	{
		CoordType t1, t2;
		Point tp = p2 - p1;
		CoordType d = d1.y * d2.x - d1.x * d2.y;			//Cramer's Rule
		CoordType dx = tp.y * d2.x - tp.x * d2.y;
		CoordType dy = tp.y * d1.x - tp.x * d1.y;
		t1 = dx / d;
		t2 = dy / d;
		if (t1 >= CoordType(0) && t2 >= CoordType(0))
		{
			if (t1 > t2)
			{
				ip = p1 + d1 * t1;
			}
			else
			{
				ip = p2 + d2 * t2;
			}

		}

	}
	return ip;
}

struct DCELVertex;
struct DCELEdge;
struct DCELFace;

struct DCELVertex
{
	shared_ptr<DCELEdge> incEdge;
	Point p;
	bool isValid;
	shared_ptr<DCELFace> incSite; //site with the smallest id

	DCELVertex(const Point& _p, shared_ptr<DCELEdge> _incEdge = nullptr) :p(_p), incEdge(_incEdge), incSite(nullptr), isValid(true)
	{

	}
};


struct DCELEdge
{
	shared_ptr<DCELEdge> twin, pred, succ;
	shared_ptr<DCELVertex> origin;
	shared_ptr<DCELFace> incFace;
	Point direction;
	Point point;
	bool isValid;

	list<shared_ptr<DCELEdge>>::iterator listIter;


	DCELEdge(const Point& _direction, const Point& _point, shared_ptr<DCELFace> _incFace = nullptr, shared_ptr<DCELEdge> _twin = nullptr, shared_ptr<DCELEdge> _pred = nullptr, shared_ptr<DCELEdge> _succ = nullptr, shared_ptr<DCELVertex> _origin = nullptr)
		:direction(_direction), point(_point), twin(_twin), pred(_pred), succ(_succ), origin(_origin), incFace(_incFace), isValid(true)
	{

	}
};


struct DCELFace
{
	int id;
	Point sitePos;
	shared_ptr<DCELEdge> incEdge;
	vector<shared_ptr<DCELEdge>> infEdges;

	DCELFace(int _id, const Point& _sitePos) :id(_id), sitePos(_sitePos), incEdge(nullptr)
	{

	}
};

struct BreakPoint;

struct Event
{
	enum Kind { SiteEvent, CircleEvent } kind;
	shared_ptr<DCELFace> site;
	set<BreakPoint>::iterator lbpIter, rbpIter;
	Point circleCenter;
	Event(Kind _kind, shared_ptr<DCELFace> _site) :kind(_kind), site(_site)
	{
		assert(kind == SiteEvent);
	}

	Event(Kind _kind, set<BreakPoint>::iterator _lbpIter, set<BreakPoint>::iterator _rbpIter, const Point& _circleCenter)
		:kind(_kind), lbpIter(_lbpIter), rbpIter(_rbpIter), circleCenter(_circleCenter)
	{
		assert(kind == CircleEvent);
	}
};

struct BreakPoint
{
	static CoordType curSweepLineY;
	shared_ptr<DCELFace> leftSite, rightSite;
	shared_ptr<DCELEdge> incEdge; //保存的是leftSite在incEdge左侧的那条半边
	Point direction;	//实际移动方向
	mutable Point point;
	mutable CoordType sweepLineY;
	mutable map<Point, Event>::iterator leftArcEvent, rightArcEvent;
	bool isLeft; //是否是两抛物线交点靠左的那个

	BreakPoint(shared_ptr<DCELFace> _leftSite, shared_ptr<DCELFace> _rightSite, CoordType _pointX, CoordType _sLY, map<Point, Event>::iterator endIter, shared_ptr<DCELEdge> _incEdge = nullptr, bool _isLeft = false)
		:leftSite(_leftSite), rightSite(_rightSite), point(_pointX, 0), sweepLineY(_sLY), isLeft(_isLeft), incEdge(_incEdge), leftArcEvent(endIter), rightArcEvent(endIter)
	{
		if (incEdge != nullptr)
		{
			if (incEdge->direction.x > CoordType(0))
			{
				direction = isLeft ? -incEdge->direction : incEdge->direction;
			}
			else if (incEdge->direction.x < CoordType(0))
			{
				direction = isLeft ? incEdge->direction : -incEdge->direction;
			}
			else
			{
				direction = Point(0, -1);
			}
		}

	}

	BreakPoint(CoordType _pointX) :point(_pointX, 0), sweepLineY(COORD_NINF)
	{

	}

	CoordType getPointX() const
	{
		return getPoint().x;
	}

	Point getPoint() const
	{
		if (sweepLineY > curSweepLineY)			//计算交点的方法为将两个抛物线焦点的中垂线与其中一条抛物线求交
		{
			Point p = (leftSite->sitePos + rightSite->sitePos) / 2;
			Point direction(leftSite->sitePos.y - rightSite->sitePos.y, rightSite->sitePos.x - leftSite->sitePos.x);
			direction.normalize();
			Point tp = p - leftSite->sitePos;
			CoordType a = direction.x * direction.x;
			CoordType b = (direction.dot(tp) + direction.y *(curSweepLineY - p.y)) * 2;
			CoordType c = tp.dot(tp) - (curSweepLineY - p.y) *(curSweepLineY - p.y);
			if (direction.x == 0)
			{
				//assert(b != CoordType(0));	//若其他部分实现正确，交点消失必然会在一个事件中被处理, 从而不会存在这个断点
				CoordType t = -c / b;
				point = p + direction * t;
			}
			else
			{
				CoordType delta = b * b - a * c * 4;
				//assert(delta >= CoordType(0)); //若其他部分实现正确，交点消失必然会在一个事件中被处理, 从而不会存在这个断点
				delta = sqrt(delta);
				CoordType t1 = (-b + delta) / (a * 2);
				CoordType t2 = (-b - delta) / (a * 2);
				CoordType x1 = p.x + t1 * direction.x;
				CoordType x2 = p.x + t2 * direction.x;
				if (isLeft)
				{
					point = p + direction * (x1 < x2 ? t1 : t2);
				}
				else
				{
					point = p + direction * (x1 < x2 ? t2 : t1);
				}

			}
			sweepLineY = curSweepLineY;
		}
		return point;
	}

	bool operator<(const BreakPoint& bp) const
	{
		return getPointX() < bp.getPointX() || (getPointX() == bp.getPointX() && ((leftSite->id == bp.rightSite->id && rightSite->id == bp.leftSite->id) ? isLeft : rightSite->id == bp.leftSite->id));
	}
};

CoordType BreakPoint::curSweepLineY = COORD_PINF;



class VoronoiDiagram
{
	vector<shared_ptr<DCELVertex>> voronoiVertices;
	vector<shared_ptr<DCELEdge>> voronoiEdges;
	vector<shared_ptr<DCELFace>> voronoiFaces;
	map<Point, Event> eventQueue; //想好是否用PQ 处理多个点共圆时 可能需要允许相同位置的圆事件？
	set<BreakPoint> beachLine;

	shared_ptr<DCELVertex> infVertex;
	shared_ptr<DCELFace> infFace;

	vector<shared_ptr<DCELVertex>> boundaryVertices[4];

	vector<vector<shared_ptr<DCELEdge>>> slabStructure;


	void findCircleEvent(set<BreakPoint>::iterator bp1Iter, set<BreakPoint>::iterator bp2Iter) //圆事件可能发生的条件为断点对应的边有汇聚趋势且圆的最低点在扫描线下方
	{
		//todo: 退化情形

		//assert(bp1Iter->rightArcEvent == eventQueue.end());
		//assert(bp2Iter->leftArcEvent == eventQueue.end());	//assert failure leads to infinite loop?

		Point potentialCenter = intersect(bp1Iter->getPoint(), bp1Iter->direction, bp2Iter->getPoint(), bp2Iter->direction);

		if (potentialCenter != POINT_INF)
		{
			Point eventPoint = potentialCenter;
			CoordType handedness = (eventPoint - bp1Iter->getPoint()).cross(bp2Iter->getPoint() - bp1Iter->getPoint());
			eventPoint.y -= (potentialCenter - bp1Iter->leftSite->sitePos).norm();
			if (handedness >= CoordType(0) && eventPoint.y <= BreakPoint::curSweepLineY && eventPoint.y > COORD_NINF)
			{
				auto insertInfo = eventQueue.emplace(eventPoint, Event(Event::CircleEvent, bp1Iter, bp2Iter, potentialCenter));
				if (insertInfo.second)
				{
					bp1Iter->rightArcEvent = bp2Iter->leftArcEvent = insertInfo.first;
				}
				else //多点共圆
				{
					Event &e = insertInfo.first->second;
					if ((*bp1Iter) < *e.lbpIter)
					{
						e.lbpIter = bp1Iter;
					}
					if (*e.rbpIter < (*bp2Iter))
					{
						e.rbpIter = bp2Iter;
					}
					modifyCircleEventAssoc(e, insertInfo.first);
				}

			}
		}

	}

	shared_ptr<DCELEdge> makeEdge(shared_ptr<DCELFace> s1, shared_ptr<DCELFace> s2) //返回的边的incFace是s1(s1在其左边）
	{
		//注意要同时构造出twin edge, 并将edge与face关联
		Point direction(s1->sitePos.y - s2->sitePos.y, s2->sitePos.x - s1->sitePos.x);
		Point midPoint = (s1->sitePos + s2->sitePos) / 2;
		direction.normalize();
		if (direction.cross(s1->sitePos - midPoint) < 0)
		{
			direction = -direction;
		}
		shared_ptr<DCELEdge> e = make_shared<DCELEdge>(direction, midPoint, s1);
		shared_ptr<DCELEdge> te = make_shared<DCELEdge>(-direction, midPoint, s2, e);
		voronoiEdges.push_back(e);
		voronoiEdges.push_back(te);
		e->twin = te;
		if (s1->incEdge = nullptr)
		{
			s1->incEdge = e;
		}
		if (s2->incEdge = nullptr)
		{
			s2->incEdge = te;
		}
		return e;
	}

	void modifyCircleEventAssoc(const Event& e, map<Point, Event>::iterator eIter)
	{
		e.lbpIter->rightArcEvent = eIter;
		e.rbpIter->leftArcEvent = eIter;
		auto it = e.lbpIter;
		for (it++; it != e.rbpIter; it++)
		{
			it->leftArcEvent = it->rightArcEvent = eIter;
		}
	}

	void removeCircleEventAssoc(const Event& e)
	{
		modifyCircleEventAssoc(e, eventQueue.end());
	}

	bool checkIntersectionSide(const Point& p, const Point& leftSitePos, const Point& rightSitePos)  //true:left false:right 
	{
		return leftSitePos.y < rightSitePos.y ? (p.x < leftSitePos.x) : (p.x < rightSitePos.x);
	}

	bool boundaryHelper(int i, Point& ip, const Point& p, const Point&d)
	{
		switch (i)
		{
		case 0:
			ip.x = COORD_NINF;
			ip.y = p.y + (ip.x - p.x) * d.y / d.x;
			return ip.y < COORD_PINF && ip.y > COORD_NINF;
		case 1:
			ip.x = COORD_PINF;
			ip.y = p.y + (ip.x - p.x) * d.y / d.x;
			return ip.y < COORD_PINF && ip.y > COORD_NINF;
		case 2:
			ip.y = COORD_PINF;
			ip.x = p.x + (ip.y - p.y) * d.x / d.y;
			return ip.x < COORD_PINF && ip.y > COORD_NINF;
		case 3:
			ip.y = COORD_NINF;
			ip.x = p.x + (ip.y - p.y) * d.x / d.y;
			return ip.x < COORD_PINF && ip.y > COORD_NINF;
		default:
			assert(false);
			return false;
		}
	}

	void intersectWithBoundary(shared_ptr<DCELEdge> edge)
	{
		Point ip1, ip2;
		Point &d = edge->direction;
		Point &p = edge->point;
		if (d.x == 0)
		{
			ip1.x = ip2.x = p.x;
			ip1.y = COORD_PINF;
			ip2.y = COORD_NINF;
		}
		else if (d.y == 0)
		{
			ip1.y = ip2.y = p.y;
			ip1.x = COORD_NINF;
			ip2.x = COORD_PINF;
		}
		else
		{
			int side = 0;
			for (; side < 4 && !boundaryHelper(side, ip1, p, d); side++);
			for (side++; side < 4 && !boundaryHelper(side, ip2, p, d); side++);
		}

		shared_ptr<DCELVertex> v1 = make_shared<DCELVertex>(ip1), v2 = make_shared<DCELVertex>(ip2);

		if (edge->twin->origin == nullptr)
		{
			voronoiVertices.emplace_back(v1);
			voronoiVertices.emplace_back(v2);
			boundaryVertices[boundaryId(ip1)].emplace_back(v1);
			boundaryVertices[boundaryId(ip2)].emplace_back(v2);
			Point td = ip2 - ip1;
			td.normalize();
			if (td == d)
			{
				edge->origin = v1;
				v1->incEdge = edge;
				edge->twin->origin = v2;
				v2->incEdge = edge->twin;
			}
			else
			{
				edge->origin = v2;
				v2->incEdge = edge;
				edge->twin->origin = v1;
				v1->incEdge = edge->twin;
			}
		}
		else
		{
			Point td = edge->twin->origin->p - ip1;
			td.normalize();
			if (td == d)
			{
				voronoiVertices.emplace_back(v1);
				boundaryVertices[boundaryId(ip1)].emplace_back(v1);
				edge->origin = v1;
				v1->incEdge = edge;
			}
			else
			{
				voronoiVertices.emplace_back(v2);
				boundaryVertices[boundaryId(ip2)].emplace_back(v2);
				edge->origin = v2;
				v2->incEdge = edge;
			}
		}
	}

	static int boundaryId(const Point& p)
	{
		return p.x * p.x == COORD_PINF * COORD_PINF ? (p.x > CoordType(0) ? 1 : 3) : (p.y > CoordType(0) ? 2 : 0);
	}

	static bool compareForBoundaryVertices(shared_ptr<DCELVertex> v1, shared_ptr<DCELVertex> v2)
	{
		switch (boundaryId(v1->p))
		{
		case 0:
			return v1->p.x < v2->p.x;
		case 1:
			return v1->p.y < v2->p.y;
		case 2:
			return v1->p.x > v2->p.x;
		case 3:
			return v1->p.y > v2->p.y;
		default:
			assert(false);
			return false;
		}
	}

	void chain(shared_ptr<DCELEdge> predEdge, shared_ptr<DCELEdge> succEdge)
	{
		predEdge->succ = succEdge;
		succEdge->pred = predEdge;
	}
public:
	VoronoiDiagram() :infVertex(new DCELVertex(POINT_INF)), infFace(new DCELFace(1e9, infVertex->p))
	{

	}

	void addSite(const Point &p, int id)
	{
		voronoiFaces.push_back(make_shared<DCELFace>(id, p));
		eventQueue.emplace(p, Event(Event::SiteEvent, voronoiFaces.back()));
	}

	void constructVD()
	{

		while (eventQueue.size() > 0)
		{
			auto iter = eventQueue.begin();
			Point ep = iter->first;
			Event &event = iter->second;
			BreakPoint::curSweepLineY = ep.y;


			if (iter->second.kind == Event::Kind::SiteEvent)
			{
				if (beachLine.size() == 0)	//handle degeneracy
				{
					auto eventIter = eventQueue.begin();
					CoordType ty = ep.y;
					BreakPoint leftmost(nullptr, event.site, CoordType(-numeric_limits<double>::infinity()), COORD_NINF, eventQueue.end());
					beachLine.insert(leftmost);
					auto lastEventIter = eventIter;
					eventIter++;
					while (eventIter != eventQueue.end() && eventIter->first.y == ty)
					{
						shared_ptr<DCELEdge> edge = makeEdge(lastEventIter->second.site, eventIter->second.site);
						CoordType x = (lastEventIter->second.site->sitePos.x + eventIter->second.site->sitePos.x) / 2;
						BreakPoint bp(lastEventIter->second.site, eventIter->second.site, x, COORD_NINF, eventQueue.end(), edge, true);
						beachLine.insert(bp);
						lastEventIter = eventIter;
						eventIter++;
					}
					BreakPoint rightmost(lastEventIter->second.site, nullptr, CoordType(numeric_limits<double>::infinity()), COORD_NINF, eventQueue.end());
					beachLine.insert(rightmost);
					eventQueue.erase(eventQueue.begin(), lastEventIter);
					for (const BreakPoint& bp : beachLine)
					{
						bp.sweepLineY = COORD_PINF;
					}
					beachLine.begin()->sweepLineY = COORD_NINF;
					beachLine.rbegin()->sweepLineY = COORD_NINF;
				}
				else
				{
					auto rightIter = beachLine.upper_bound(BreakPoint(ep.x));
					auto leftIter = rightIter;
					--leftIter;

					shared_ptr<DCELEdge> edge = makeEdge(event.site, leftIter->rightSite);
					BreakPoint lbp(leftIter->rightSite, event.site, ep.x, COORD_PINF, eventQueue.end(), edge->twin, true), rbp(event.site, rightIter->leftSite, ep.x, COORD_PINF, eventQueue.end(), edge, false);

					if (leftIter->rightArcEvent != eventQueue.end())
					{
						auto eIter = leftIter->rightArcEvent;
						removeCircleEventAssoc(eIter->second);
						eventQueue.erase(eIter);
					}

					auto lbpIter = beachLine.insert(lbp).first;
					auto rbpIter = beachLine.insert(rbp).first;

					auto llIter = leftIter, rrIter = rightIter;
					--llIter;
					++rrIter;
					if (llIter != beachLine.end())
					{
						findCircleEvent(leftIter, lbpIter);
					}
					if (rrIter != beachLine.end())
					{
						findCircleEvent(rbpIter, rightIter);
					}
				}

			}
			else  //CircleEvent
			{
				//Todo: 处理退化情况

				//event.circleCenter = event.lbpIter->getPoint();

				shared_ptr<DCELVertex> v = make_shared<DCELVertex>(event.circleCenter, event.lbpIter->incEdge);
				voronoiVertices.push_back(v);
				shared_ptr<DCELEdge> e = makeEdge(event.lbpIter->leftSite, event.rbpIter->rightSite);
				auto itEnd = event.rbpIter;
				itEnd++;
				shared_ptr<DCELEdge> lastEdge = e;
				for (auto it = event.lbpIter; it != itEnd; it++)
				{
					it->incEdge->origin = v;
					chain(lastEdge, it->incEdge);
					lastEdge = it->incEdge->twin;
				}
				e->twin->origin = v;
				chain(lastEdge, e->twin);
				removeCircleEventAssoc(iter->second);


				BreakPoint bp(event.lbpIter->leftSite, event.rbpIter->rightSite, event.circleCenter.x, BreakPoint::curSweepLineY, eventQueue.end(), e, checkIntersectionSide(event.circleCenter, event.lbpIter->leftSite->sitePos, event.rbpIter->rightSite->sitePos));
				bp.point.y = event.circleCenter.y;
				if (event.lbpIter->leftArcEvent != eventQueue.end())
				{
					auto eIter = event.lbpIter->leftArcEvent;
					removeCircleEventAssoc(eIter->second);
					eventQueue.erase(eIter);
				}
				if (event.rbpIter->rightArcEvent != eventQueue.end())
				{
					auto eIter = event.rbpIter->rightArcEvent;
					removeCircleEventAssoc(eIter->second);
					eventQueue.erase(eIter);
				}
				beachLine.erase(event.lbpIter, itEnd);
				auto bpIter = beachLine.insert(bp).first;
				auto lIter = bpIter, rIter = bpIter;
				lIter--;
				rIter++;

				if (lIter != beachLine.end() && lIter->leftSite != nullptr)
				{
					//assert(lIter->rightArcEvent == eventQueue.end());
					//assert(bpIter->leftArcEvent == eventQueue.end());
					findCircleEvent(lIter, bpIter);
				}
				if (rIter != beachLine.end() && rIter->rightSite != nullptr)
				{
					//assert(bpIter->rightArcEvent == eventQueue.end());
					//assert(rIter->leftArcEvent == eventQueue.end());
					findCircleEvent(bpIter, rIter);
				}
			}
			eventQueue.erase(eventQueue.begin());
		}

		//remove vertices that are out of boundary
		for (shared_ptr<DCELVertex> v : voronoiVertices)
		{
			if (!isFinite(v->p))
			{
				v->isValid = false;
				shared_ptr<DCELEdge> te = v->incEdge;
				do
				{
					Point ip1, ip2;
					Point &d = te->direction;
					Point &p = te->point;
					if (d.x == 0)
					{
						ip1.x = ip2.x = p.x;
						ip1.y = COORD_PINF;
						ip2.y = COORD_NINF;
					}
					else if (d.y == 0)
					{
						ip1.y = ip2.y = p.y;
						ip1.x = COORD_NINF;
						ip2.x = COORD_PINF;
					}
					else
					{
						int side = 0;
						for (; side < 4 && !boundaryHelper(side, ip1, p, d); side++);
						for (side++; side < 4 && !boundaryHelper(side, ip2, p, d); side++);
					}

					Point td = ip1 - te->origin->p;
					td.normalize();
					if (td != d)
					{
						te->isValid = te->twin->isValid = false;
					}

					te->origin = nullptr;
					te = te->twin->succ;

				} while (std::operator!=(te, v->incEdge));
			}


		}


		//handle infinite edegs 

		for (shared_ptr<DCELEdge> e : voronoiEdges)
		{
			if (e->origin == nullptr && e->isValid)
			{
				intersectWithBoundary(e); //未处理退化情形 但是随机选取边界 就可以避免交点在角上的退化情形（现在是正方形边界 需要修改为长方形边界）
			}
		}

		//erase invalid vertices and edges from vector
		{
			vector<shared_ptr<DCELVertex>> vtvec;
			vector<shared_ptr<DCELEdge>> etvec;
			for (shared_ptr<DCELVertex> v : voronoiVertices)
			{
				if (v->isValid)
				{
					vtvec.emplace_back(v);
				}
			}
			voronoiVertices.swap(vtvec);
			for (shared_ptr<DCELEdge> e : voronoiEdges)
			{
				if (e->isValid)
				{
					etvec.emplace_back(e);
				}
			}
			voronoiEdges.swap(etvec);
		}


		//construct bounding box 

		shared_ptr<DCELVertex> cornerVertices[4];
		Point bdirection[4];
		bdirection[0] = Point(1, 0);
		bdirection[1] = Point(0, 1);
		bdirection[2] = Point(-1, 0);
		bdirection[3] = Point(0, -1);

		cornerVertices[0] = make_shared<DCELVertex>(Point(COORD_NINF, COORD_NINF));
		cornerVertices[1] = make_shared<DCELVertex>(Point(COORD_PINF, COORD_NINF));
		cornerVertices[2] = make_shared<DCELVertex>(Point(COORD_PINF, COORD_PINF));
		cornerVertices[3] = make_shared<DCELVertex>(Point(COORD_NINF, COORD_PINF));
		for (int i = 0; i < 4; i++)
		{
			voronoiVertices.emplace_back(cornerVertices[i]);
		}

		int ti;
		for (ti = 0; ti < 4 && boundaryVertices[ti].size() == 0; ti++);

		for (int i = 0; i < 4; i++)
		{
			int curSide = (ti + i) % 4;
			vector<shared_ptr<DCELVertex>>& tvec = boundaryVertices[curSide];
			shared_ptr<DCELVertex> cvertex = cornerVertices[curSide];
			Point& td = bdirection[curSide];
			sort(tvec.begin(), tvec.end(), compareForBoundaryVertices);
			shared_ptr<DCELVertex> lastVertex = cvertex;
			for (shared_ptr<DCELVertex> v : tvec)
			{
				shared_ptr<DCELEdge> e = make_shared<DCELEdge>(td, lastVertex->p);
				shared_ptr<DCELEdge> te = make_shared<DCELEdge>(-td, lastVertex->p);
				voronoiEdges.emplace_back(e);
				voronoiEdges.emplace_back(te);
				e->origin = lastVertex;
				te->origin = v;
				te->incFace = infFace;
				e->incFace = v->incEdge->incFace;
				e->twin = te;
				te->twin = e;
				chain(e, v->incEdge);
				if (std::operator!=(lastVertex, cornerVertices[ti]))
				{
					chain(lastVertex->incEdge->twin, e);
					if (std::operator!=(lastVertex, cornerVertices[curSide]))
					{
						chain(te, lastVertex->incEdge->pred->twin);
					}
					else
					{
						chain(te, lastVertex->incEdge);
					}
				}
				lastVertex = v;
			}

			shared_ptr<DCELEdge> le = make_shared<DCELEdge>(td, lastVertex->p);
			shared_ptr<DCELEdge> lte = make_shared<DCELEdge>(-td, lastVertex->p);
			voronoiEdges.emplace_back(le);
			voronoiEdges.emplace_back(lte);
			le->origin = lastVertex;
			lte->origin = cornerVertices[(ti + i + 1) % 4];
			cornerVertices[(ti + i + 1) % 4]->incEdge = lte;
			lte->incFace = infFace;
			le->incFace = lastVertex->incEdge->twin->incFace;
			le->twin = lte;
			lte->twin = le;
			chain(lastVertex->incEdge->twin, le);
			if (std::operator!=(lastVertex, cornerVertices[i]))
			{
				chain(lte, lastVertex->incEdge->pred->twin);
			}
			else if (i != 0)
			{
				chain(lte, lastVertex->incEdge);
			}


			if (i == (ti + 3) % 4)
			{
				auto temp = (*(boundaryVertices[ti].begin()))->incEdge->pred;
				chain(le, temp);
				chain(temp->twin, lte);
			}
		}

	}

	void constrcutSlabDecomposition()
	{
		//首先找到每个DCELVertex的邻近的编号最小的site，以方便处理查询点与DCELVertex重合的情形
		for (shared_ptr<DCELVertex> v : voronoiVertices)
		{
			shared_ptr<DCELEdge> e = v->incEdge;
			shared_ptr<DCELFace> f = e->incFace;
			e = e->twin->succ;
			while (std::operator!=(e, v->incEdge))
			{
				if (e->incFace->id < f->id)
				{
					f = e->incFace;
				}
				e = e->twin->succ;
			}
			v->incSite = f;
		}

		sort(voronoiVertices.begin(), voronoiVertices.end(), [](shared_ptr<DCELVertex> a, shared_ptr<DCELVertex> b)->bool
		{
			return a->p < b->p;
		});

		list<shared_ptr<DCELEdge>> elist;
		for (shared_ptr<DCELEdge> e : voronoiEdges)
		{
			e->listIter = elist.end();
		}
		for (shared_ptr<DCELVertex> v : voronoiVertices)
		{
			bool(*upwardPointing)(const Point&) = [](const Point& d)->bool {return d.y > CoordType(0) || (d.x == -1 && d.y == CoordType(0)); };
			shared_ptr<DCELEdge> te = v->incEdge;
			shared_ptr<DCELEdge> upwardLeftmost = nullptr, downwardLeftmost = nullptr;		//只有第一个点和最后一个点会发生这两个变量为nullptr的情况，因为中间的点都有前驱和后继从而存在向上指和向下指的边
			if (upwardPointing(te->direction))
			{
				do
				{
					upwardLeftmost = te;
					te = te->pred->twin;
				} while (upwardPointing(te->direction) && upwardLeftmost->direction.cross(te->direction) > CoordType(0));
				if (!upwardPointing(te->direction))
				{
					downwardLeftmost = te;
				}
			}
			else
			{
				do
				{
					downwardLeftmost = te;
					te = te->twin->succ;
				} while (!upwardPointing(te->direction) && downwardLeftmost->direction.cross(te->direction) < CoordType(0));
				if (upwardPointing(te->direction))
				{
					upwardLeftmost = te;
				}
			}


			list<shared_ptr<DCELEdge>>::iterator insertPos = elist.end();
			if (upwardLeftmost != nullptr)
			{
				list<shared_ptr<DCELEdge>>::iterator eraseBegin = upwardLeftmost->twin->listIter;
				list<shared_ptr<DCELEdge>>::iterator eraseEnd = eraseBegin;
				++eraseEnd;
				while (eraseEnd != elist.end() && (*eraseEnd)->twin->origin == v)
				{
					++eraseEnd;
				}
				insertPos = elist.erase(eraseBegin, eraseEnd);
			}

			if (downwardLeftmost != nullptr)
			{
				te = downwardLeftmost;
				do
				{
					te->listIter = elist.insert(insertPos, te);
					insertPos = te->listIter;
					++insertPos;
					te = te->pred->twin;
				} while (!upwardPointing(te->direction) && te->listIter == elist.end());
			}

			slabStructure.emplace_back();
			vector<shared_ptr<DCELEdge>> &vec = slabStructure.back();
			for (shared_ptr<DCELEdge> e : elist)
			{
				vec.emplace_back(e);
			}
		}
	}

	int closestSite(const Point& p)
	{
		vector<shared_ptr<DCELVertex>>::iterator vIter = lower_bound(voronoiVertices.begin(), voronoiVertices.end(), p, [](shared_ptr<DCELVertex> a, const Point& b)->bool
		{
			return a->p < b;
		});

		if ((*vIter)->p == p)
		{
			return (*vIter)->incSite->id;
		}


		int index = vIter - voronoiVertices.begin() - 1;
		vector<shared_ptr<DCELEdge>>& slab = slabStructure[index];
		vector<shared_ptr<DCELEdge>>::iterator eIter = lower_bound(slab.begin(), slab.end(), p, [](shared_ptr<DCELEdge> a, const Point& b)->bool
		{
			return a->direction.cross(b - a->origin->p) > CoordType(0);
		});

		if ((*eIter)->direction.cross(p - (*eIter)->origin->p) == 0)
		{
			return min((*eIter)->incFace->id, (*eIter)->twin->incFace->id);
		}

		return (*eIter)->twin->incFace->id;
	}
};


int main()
{
	setvbuf(stdin, new char[1 << 20], _IOFBF, 1 << 20);
	setvbuf(stdout, new char[1 << 20], _IOFBF, 1 << 20);

	int nBoy, nGirl;
	VoronoiDiagram vd;
	scanf("%d", &nBoy);
	int x, y;
	for (int i = 0; i < nBoy; i++)
	{
		scanf("%d %d", &x, &y);
		vd.addSite(Point(x, y), i);
	}
	vd.constructVD();
	vd.constrcutSlabDecomposition();
	scanf("%d", &nGirl);
	for (int i = 0; i < nGirl; i++)
	{
		scanf("%d %d", &x, &y);
		printf("%d\n", vd.closestSite(Point(x, y)));
	}

	return 0;
}