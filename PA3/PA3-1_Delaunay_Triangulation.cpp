/**
 *

 Construct Delaunay Triangulation with simplified DCEL representation using RIC(Randomized Incremental Construction) in expected-O(nlogn) time.

 ��Ҫע��������һЩʵ��ϸ�ڣ�
 1.���ڵ�Ĳ���˳��������ģ�����ĵ�������ڵ�ǰ������ĵ㼯��͹���⣬��������Ĵ������һ���������ڲ��Ĵ���ͬ��Ϊ�˷�����������ǿ��Լ���������Զ�ĵ㣬��������͵㼯����ߵ㹹�ɵ���������ȫ�������ǵ㼯�����뷶Χ����������ȷ��ÿ���¼���ĵ㶼λ��һ�����ڵ��������ڲ���ͬʱ�������㲻�����κ�һ���㼯�������ε����Բ�ڣ�������֤������ǿ���ͨ��ɾ����������Զ�����õ�������Ҫ��Delaunay Triangulation�����ǲ�����Ϊ�������㱣��޴������ֵ����Ϊ�������ܻ��˷Ѽ��㾫�ȡ�����ʵ��ϸ�ڿɲ鿴CGAA��Ӧ�½�

   !!!CGAA���жϱߵĺϷ���Ĭ���˲��Զ������͹����Σ��ر��ǵ�������������Ҫ����԰�����Σ����������Σ�������жϣ����ı���ʱ����edge flip)


 2.����һ�����������ǲ���ĵ�����������������εı߽��ϡ����Ǽ���������������ڵ�����һ���������ڲ�������ֻҪ��in-circle test��ʵ���м��Բ�ϵ����㹲�ߵ��������Ӧһ��������Բ���������Ϳ��Ա�֤���ڱ��ϵĵ������Ȼ����һ��edge flip�����������ڱ���ֱ�����������������������������ǵ�Ч��

 

 */

#include<iostream>
#include<algorithm>
#include<vector>
#include<list>
#include<memory>
#include<random>
#include<queue>

using namespace std;

struct DCELVertex;
struct DCELHalfEdge;
struct GraphNode;

using GNptr = shared_ptr<GraphNode>;
using Vptr = shared_ptr<DCELVertex>;
using HEptr = shared_ptr<DCELHalfEdge>;


using CoordType = long long int;

struct Point
{
	CoordType x, y;
	int id;
	Point(CoordType _x = 0, CoordType _y = 0, int _id = -3) :x(_x), y(_y), id(_id)
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
		return this->y < other.y || this->y == other.y && this->x < other.x;
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

struct DCELVertex
{
	//HEptr incHalfEdge;
	Point p;

	DCELVertex(const Point& _p) :p(_p)
	{

	}
};



struct DCELHalfEdge
{
	HEptr twin, pred, succ;
	Vptr origin;
	GNptr incNode;

	DCELHalfEdge(Vptr v) :origin(v)
	{

	}
};

struct GraphNode
{
	Vptr v1, v2, v3;			//ccw order
	HEptr he;			//halfedge from v1 to v2
	vector<GNptr> childrens;

	GraphNode(Vptr _v1, Vptr _v2, Vptr _v3, HEptr _he) :v1(_v1), v2(_v2), v3(_v3), he(_he)
	{

	}
};




class DelaunayTriangulation
{
	vector<HEptr> halfEdges;
	GNptr searchRoot;



	HEptr newEdge(Vptr v1, Vptr v2)  //return the new halfedge whose origin is v1
	{
		auto he1 = make_shared<DCELHalfEdge>(v1);
		auto he2 = make_shared<DCELHalfEdge>(v2);
		halfEdges.push_back(he1);
		halfEdges.push_back(he2);
		he1->twin = he2;
		he2->twin = he1;

		return he1;
	}

	void chain(HEptr predHE, HEptr succHE)
	{
		predHE->succ = succHE;
		succHE->pred = predHE;
	}

	void flipEdge(HEptr he0)
	{
		HEptr he1 = he0->succ, he2 = he1->succ, he3 = he0->twin, he4 = he3->succ, he5 = he4->succ;

		auto f1 = make_shared<GraphNode>(he2->origin, he4->origin, he5->origin, he2);
		auto f2 = make_shared<GraphNode>(he5->origin, he1->origin, he2->origin, he5);


		he0->incNode->childrens.push_back(f1);
		he0->incNode->childrens.push_back(f2);
		he3->incNode->childrens.push_back(f1);
		he3->incNode->childrens.push_back(f2);

		//he1->origin->incHalfEdge = he1;
		//he2->origin->incHalfEdge = he2;
		//he4->origin->incHalfEdge = he4;
		//he5->origin->incHalfEdge = he5;

		he1->incNode = he5->incNode = he0->incNode = f2;
		he2->incNode = he3->incNode = he4->incNode = f1;
		he0->origin = he2->origin;
		he3->origin = he5->origin;
		chain(he0, he5); chain(he5, he1); chain(he1, he0);
		chain(he3, he2); chain(he2, he4); chain(he4, he3);

	}

	GNptr pointLocation(const Point& p)
	{
		auto inTriangleTest = [](const Point&p, GNptr node) 
		{
			auto edgeTest = [](const Point& p, const Point& p1, const Point& p2)
			{
				
				if (p1.id<0 && p2.id<0)
				{
					return true;
				}
				else if (min(p1.id, p2.id) < 0)
				{
					if (p1.id < 0)
					{
						return p1.id == -2 ? p2 < p : p < p2;
					}
					else
					{
						return p2.id == -2 ? p < p1 : p1 < p;
					}
				}
				else
				{
					return (p2 - p1).cross(p - p1) >= 0;
				}
			};
			
			return edgeTest(p, node->v1->p, node->v2->p) && edgeTest(p, node->v2->p, node->v3->p) && edgeTest(p, node->v3->p, node->v1->p);
		};

		auto curNode = searchRoot;
		while (curNode->childrens.size() > 0)
		{
			for (auto node : curNode->childrens)
			{
				if (inTriangleTest(p, node))
				{
					curNode = node;
					continue;
				}
			}
		}
		return curNode;
	}

	bool inCircleTest(const Point& tp, const Point& p1, const Point& p2, const Point& p3)
	{
		if ((p3 - p2).cross(p2 - p1) == 0)   //colinear case
		{
			return true;
		}

		auto calDet3x3 = [](double a11, double a12, double a13,
			double a21, double a22, double a23,
			double a31, double a32, double a33)
		{
			return a11 * a22*a33 + a12 * a23*a31 + a13 * a21*a32 - a13 * a22*a31 - a12 * a21*a33 - a11 * a23*a32;
		};

		Point tp1 = p1 - tp, tp2 = p2 - tp, tp3 = p3 - tp;
		return calDet3x3(tp1.x, tp1.y, tp1.x*tp1.x + tp1.y*tp1.y,
			tp2.x, tp2.y, tp2.x*tp2.x + tp2.y*tp2.y,
			tp3.x, tp3.y, tp3.x*tp3.x + tp3.y*tp3.y) > 0;

	}
public:
	DelaunayTriangulation(int n)
	{
		vector<Point> points;
		CoordType x, y;
		Point highestInputPoint(-1000000, -1000000);
		int pos = 0;


		//input handling
		for (int i = 1; i <= n; ++i)
		{
			cin >> x >> y;
			points.emplace_back(x, y, i);
			if (highestInputPoint < points.back())
			{
				highestInputPoint = points.back();
				pos = points.size();
			}
		}
		swap(points[pos - 1], points.back());
		points.pop_back();
		shuffle(points.begin(), points.end(), default_random_engine());

		//construct the first triangle
		Vptr leftmost = make_shared<DCELVertex>(Point(0,0,-2));
		Vptr rightmost = make_shared<DCELVertex>(Point(0,0,-1));
		Vptr middle = make_shared<DCELVertex>(highestInputPoint);
		HEptr l = newEdge(leftmost, rightmost), r = newEdge(rightmost, middle), m = newEdge(middle, leftmost);
		searchRoot = make_shared<GraphNode>(leftmost, rightmost, middle, l);

		//leftmost->incHalfEdge = l; rightmost->incHalfEdge = r; middle->incHalfEdge = m;

		l->incNode = m->incNode = r->incNode = searchRoot;
		chain(l, r); chain(r, m); chain(m, l);
		l = l->twin; r = r->twin; m = m->twin;
		chain(l, m); chain(m, r); chain(r, l);


		
		//insert points one by one
		queue<HEptr> mayFlipEdges;
		auto handleOneFace = [&mayFlipEdges, this](HEptr he1, HEptr he2, HEptr he3, GNptr graphNode) {
			auto f = make_shared<GraphNode>(he1->origin, he2->origin, he3->origin, he1);

			graphNode->childrens.push_back(f);

			chain(he1, he2); chain(he2, he3); chain(he3, he1);
			he1->incNode = he2->incNode = he3->incNode = f;
			mayFlipEdges.push(he1);

		};
		for (auto p : points)
		{
			auto graphNode = pointLocation(p);
			Vptr v = make_shared<DCELVertex>(p);
			HEptr vv1 = newEdge(v, graphNode->v1), vv2 = newEdge(v, graphNode->v2), vv3 = newEdge(v, graphNode->v3);
			HEptr v1v = vv1->twin, v2v = vv2->twin, v3v = vv3->twin;
			HEptr v1v2 = graphNode->he, v2v3 = v1v2->succ, v3v1 = v2v3->succ;

			//v->incHalfEdge = vv1;

			handleOneFace(v1v2, v2v, vv1, graphNode);
			handleOneFace(v2v3, v3v, vv2, graphNode);
			handleOneFace(v3v1, v1v, vv3, graphNode);

			while (mayFlipEdges.size() > 0)
			{
				HEptr he = mayFlipEdges.front();
				mayFlipEdges.pop();
				if (he->twin->incNode != nullptr)	//��������Χ�߽�
				{
					auto& p1 = he->origin->p, p2 = he->twin->origin->p, p3 = he->pred->origin->p, p4 = he->twin->pred->origin->p;

					bool doFlip = false;
					if (p1.id >= 0 && p2.id >= 0 && p3.id >= 0 && p4.id >= 0)
					{
						if (inCircleTest(p4, p1, p2, p3))
						{
							doFlip = true;
						}

					}
					else if(min(p1.id, p2.id) < min(p3.id, p4.id))
					{
						/** �ж��Ƿ��ǰ��ı��Σ�
						 		1. ����ֻ��һ����Զ�㣬�Լ�Զ��Ϊ����ĽǱ�Ȼ����ǣ�����ֻҪ�������������ķ��򼴿�
						 		2. ������������Զ�㣬��Ȼ�ǰ��ı��Σ���Ϊ�����͹�ı��Σ�������Ҫ������������ֵ��򶼱ȶԷ�С�����ǲ����ܵ�
						 */		
						if (min(p1.id, p2.id) >= 0 || min(p3.id, p4.id) >= 0)
						{
							if (p1.id < 0)
							{
								doFlip = (p2 - p4).cross(p3 - p4) > 0;
							}
							else
							{
								doFlip = (p1 - p3).cross(p4 - p3) > 0;
							}
						}
					}
					if (doFlip)
					{
						flipEdge(he);
						mayFlipEdges.push(he->succ);
						mayFlipEdges.push(he->twin->pred);
					}
				}
			}
		}
	}


	int calc()
	{
		long long int ans = 0;
		int i1, i2;
		int edgeNum = 0;
		for (auto it = halfEdges.begin();it!=halfEdges.end();it+=2)
		{
			i1 = (*it)->origin->p.id;
			i2 = (*(it + 1))->origin->p.id;
			if (i1 >= 0 && i2 >= 0)
			{
				ans += i1 + i2;
				++edgeNum;
			}
		}
		return ans % (1 + edgeNum);
	}
};

int main()
{
	int n;
	cin >> n;

	DelaunayTriangulation DT(n);
	cout << DT.calc();
	return 0;
}