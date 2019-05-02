// ConsoleApplication2.cpp : This file contains the 'main' function. Program execution begins and ends there.
//

#include <iostream>
#include <math.h>
#include <stdio.h>
#include <Windows.h>

typedef struct { double Data[3]; } V3d;

static int c_insertionSortThreshold = 31;
static int c_insertionMedianThreshold = 7;

static int c_minMerge = 32;
static int c_minGallop = 7;
static int c_initialTmpStorageLength = 256;

static int sign(double a) {
	if (a > 0.0) return 1;
	else if (a < 0.0) return -1;
	else return 0;
}

#define cmp(a,b) sign(a.Data[dim] - b.Data[dim])
#define imin(a,b) ((a) < (b) ? (a) : (b))
#define imax(a,b) ((a) > (b) ? (a) : (b))

static int PrevPowerOfTwo(int x)
{
	if (x <= 0) return 0;
	x >>= 1;
	x |= x >> 1;
	x |= x >> 2;
	x |= x >> 4;
	x |= x >> 8;
	x |= x >> 16;
	return ++x;
}
static void PermutationQuickMedianAscending1(
	long* p, V3d* a, long dim,
	long l, long r, long countSub1, long med)
{
	while (countSub1 >= c_insertionMedianThreshold)
	{
		long sixth = (1 + countSub1) / 6;
		long e1 = l + sixth;
		long e5 = r - sixth;
		long e3 = (l + r) >> 1;
		long e4 = e3 + sixth;
		long e2 = e3 - sixth;

		if (a[p[e1]].Data[dim] > a[p[e2]].Data[dim]) { auto t = p[e1]; p[e1] = p[e2]; p[e2] = t; }
		if (a[p[e4]].Data[dim] > a[p[e5]].Data[dim]) { auto t = p[e4]; p[e4] = p[e5]; p[e5] = t; }
		if (a[p[e1]].Data[dim] > a[p[e3]].Data[dim]) { auto t = p[e1]; p[e1] = p[e3]; p[e3] = t; }
		if (a[p[e2]].Data[dim] > a[p[e3]].Data[dim]) { auto t = p[e2]; p[e2] = p[e3]; p[e3] = t; }
		if (a[p[e1]].Data[dim] > a[p[e4]].Data[dim]) { auto t = p[e1]; p[e1] = p[e4]; p[e4] = t; }
		if (a[p[e3]].Data[dim] > a[p[e4]].Data[dim]) { auto t = p[e3]; p[e3] = p[e4]; p[e4] = t; }
		if (a[p[e2]].Data[dim] > a[p[e5]].Data[dim]) { auto t = p[e2]; p[e2] = p[e5]; p[e5] = t; }
		if (a[p[e2]].Data[dim] > a[p[e3]].Data[dim]) { auto t = p[e2]; p[e2] = p[e3]; p[e3] = t; }
		if (a[p[e4]].Data[dim] > a[p[e5]].Data[dim]) { auto t = p[e4]; p[e4] = p[e5]; p[e5] = t; }

		auto p1 = p[e2]; p[e2] = p[l];
		auto p2 = p[e4]; p[e4] = p[r];

		long lo = l + 1;
		long hi = r - 1;

		bool pivotsDiffer = a[p1].Data[dim] != a[p2].Data[dim];

		if (pivotsDiffer)
		{
			for (long i = lo; i <= hi; i++)
			{
				auto ai = p[i];
				if (a[ai].Data[dim] < a[p1].Data[dim]) { p[i] = p[lo]; p[lo] = ai; ++lo; }
				else if (a[ai].Data[dim] > a[p2].Data[dim])
				{
					while (a[p[hi]].Data[dim] > a[p2].Data[dim] && i < hi)
						--hi;
					p[i] = p[hi]; p[hi] = ai; --hi; ai = p[i];
					if (a[ai].Data[dim] < a[p1].Data[dim]) { p[i] = p[lo]; p[lo] = ai; ++lo; }
				}
			}
		}
		else
		{
			for (long i = lo; i <= hi; i++)
			{
				auto ai = p[i];
				if (a[ai].Data[dim] == a[p1].Data[dim]) continue;
				if (a[ai].Data[dim] < a[p1].Data[dim]) { p[i] = p[lo]; p[lo] = ai; ++lo; }
				else
				{
					while (a[p[hi]].Data[dim] > a[p1].Data[dim])
						--hi;
					p[i] = p[hi]; p[hi] = ai; --hi; ai = p[i];
					if (a[ai].Data[dim] < a[p1].Data[dim]) { p[i] = p[lo]; p[lo] = ai; ++lo; }
				}
			}
		}

		p[l] = p[lo - 1]; p[lo - 1] = p1;
		p[r] = p[hi + 1]; p[hi + 1] = p2;

		long cl = lo - 2 - l;
		long cr = r - hi - 2;

		if (pivotsDiffer)
		{
			if (lo < e1 && e5 < hi)
			{
				if (med <= lo - 2) { r = lo - 2; countSub1 = cl; }
				else if (med >= hi + 2) { l = hi + 2; countSub1 = cr; }
				else
				{
					while (a[p[lo]].Data[dim] == a[p1].Data[dim])
						++lo;
					for (long i = lo + 1; i <= hi; i++)
					{
						if (a[p[i]].Data[dim] == a[p1].Data[dim]) { p1 = p[i]; p[i] = p[lo]; p[lo] = p1; ++lo; }
					}
					while (a[p[hi]].Data[dim] == a[p2].Data[dim])
						--hi;
					for (long i = hi - 1; i >= lo; i--)
					{
						if (a[p[i]].Data[dim] == a[p2].Data[dim]) { p2 = p[i]; p[i] = p[hi]; p[hi] = p2; --hi; }
					}
					if (med < lo || med > hi) return;
					l = lo; r = hi; countSub1 = hi - lo;
				}
			}
			else
			{
				if (med <= lo - 2) { r = lo - 2; countSub1 = cl; }
				else if (med >= hi + 2) { l = hi + 2; countSub1 = cr; }
				else if (med >= lo && med <= hi) { l = lo; r = hi; countSub1 = hi - lo; }
				else return;
			}
		}
		else
		{
			if (med <= lo - 2) { r = lo - 2; countSub1 = cl; }
			else if (med >= hi + 2) { l = hi + 2; countSub1 = cr; }
			else return;
		}
	}

	for (long i = l + 1; i <= r; i++)
	{
		auto ai = p[i]; long j;
		for (j = i - 1; j >= l && a[ai].Data[dim] < a[p[j]].Data[dim]; j--)
			p[j + 1] = p[j];
		p[j + 1] = ai;
	}
}

static void PermutationQuickMedianAscending(
	long* p, V3d* a, long dim,
	long beginIncl, long endExcl, long med)
{
	PermutationQuickMedianAscending1(p, a, dim, beginIncl, endExcl - 1, endExcl - beginIncl - 1, med);
}

typedef struct {
	long Index;
	double Dist;
} IndexDist;

class ClosestToPointQuery {
public:
	V3d Point;
	int ClosestIndex;
	double ClosestDist;

	ClosestToPointQuery(V3d point) {
		Point = point;
		ClosestIndex = -1;
		ClosestDist = std::numeric_limits<double>::infinity();
	}

	void Add(IndexDist v) {
		if (v.Dist < ClosestDist) {
			ClosestIndex = v.Index;
			ClosestDist = v.Dist;
		}
	}


};


class PointRKdTreeD {
public:
	long m_dim;
	long m_size;
	double m_eps;
	V3d* m_array;
	double* m_radius;
	long* m_perm;
	long* m_axis;

	long GetMaxDim(long* perm, long start, long end)
	{
		auto min = new double[m_dim]; //.Set(double.MaxValue);
		auto max = new double[m_dim]; //.Set(double.MinValue);
		for (int i = 0; i < m_dim; i++) { min[i] = std::numeric_limits<double>::infinity(); max[i] = -std::numeric_limits<double>::infinity(); }

		for (long i = start; i < end; i++) // calculate bounding box
		{
			auto v = m_array[perm[i]];
			for (long vi = 0; vi < m_dim; vi++)
			{
				auto x = v.Data[vi];
				if (x < min[vi]) min[vi] = x;
				if (x > max[vi]) max[vi] = x;
			}
		}
		long dim = 0;
		double size = max[0] - min[0];
		for (long d = 1; d < m_dim; d++) // find max dim of box
		{
			auto dsize = max[d] - min[d];
			if (dsize > size) { size = dsize; dim = d; }
		}
		return dim;
	}

	double m_dist(V3d a, V3d b) {
		auto x = a.Data[0] - b.Data[0];
		auto y = a.Data[1] - b.Data[1];
		auto z = a.Data[2] - b.Data[2];
		return sqrt(x * x + y * y + z * z);
	}

	double GetMaxDist(
		V3d p, long* perm, long start, long end)
	{

		auto max = -std::numeric_limits<double>::infinity();
		for (long i = start; i < end; i++)
		{
			auto d = m_dist(p, m_array[perm[i]]);
			if (d > max) max = d;
		}
		return max;
	}

	void Balance(
		long* perm, long top, long left, long row,
		long start, long end)
	{
		
		if (row <= 0) { left /= 2; row = INT32_MAX; }
		if (left == 0) { m_perm[top] = perm[start]; return; }
		long mid = start - 1 + left + imin(left, row);
		long dim = GetMaxDim(perm, start, end);
		m_axis[top] = (int)dim;
		PermutationQuickMedianAscending(perm, m_array, dim, start, end, mid);
		m_perm[top] = perm[mid];
		m_radius[top] = GetMaxDist(m_array[perm[mid]], perm, start, end) + m_eps;
		if (start < mid)
			Balance(perm, 2 * top + 1, left / 2, row, start, mid);
		++mid;
		if (mid < end)
			Balance(perm, 2 * top + 2, left / 2, row - left, mid, end);
	}

	void GetClosest(ClosestToPointQuery& q, long top)
	{
		long index = m_perm[top];
		auto splitPoint = m_array[index];
		auto dist = m_dist(q.Point, splitPoint);
		long t1 = 2 * top + 1;
		auto delta = dist - q.ClosestDist;
		if (delta <= 0.0)
		{
			IndexDist rid = { index, dist };
			q.Add(rid);
		/*	q.List.HeapDescendingEnqueue(rid);
			if (q.List.Count > q.MaxCount)
			{
				q.List.HeapDescendingDequeue();
				auto md = q.List[0].Dist;
				q.MaxDist = md; q.MaxDistEps = md + m_eps;
			}*/
			if (t1 >= m_size) return;
		}
		else
		{
			if (t1 >= m_size) return;
			if (delta > m_radius[top]) return;
		}
		auto dim = m_axis[top];
		auto x = q.Point.Data[dim]; auto s = splitPoint.Data[dim];
		if (x < s)
		{
			GetClosest(q, t1);
			//auto dsi = fabs(x.Data[dim], s.Data[dim])
			if (q.ClosestDist < fabs(x - s)) return;
			long t2 = t1 + 1; if (t2 >= m_size) return;
			GetClosest(q, t2);
		}
		else
		{
			long t2 = t1 + 1;
			if (t2 < m_size) GetClosest(q, t2);
			if (q.ClosestDist < fabs(s - x)) return;
			GetClosest(q, t1);
		}
	}


	PointRKdTreeD(long size, V3d* arr, double absoluteEps) {
		m_dim = 3;
		m_size = size;
		m_eps = absoluteEps;
		m_array = arr;
		m_perm = new long[size];
		m_radius = new double[size / 2];
		m_axis = new long[size / 2];

		auto perm = new long[size];
		for (int i = 0; i < size; i++) perm[i] = i; // .SetByIndexLong(i = > i);

		long p2 = PrevPowerOfTwo(size);
		long row = size + 1 - p2; // length of last row of heap
		long left = p2 / 2; // full width of left subtree in last row

		Balance(perm, 0, left, row, 0, size);
	}
};


V3d* readV3ds(const char* file, int* cnt) {
	FILE* p_file = NULL;
	fopen_s(&p_file, file, "rb");
	if (!p_file) return nullptr;

	fseek(p_file, 0, SEEK_END);
	auto size = (size_t)ftell(p_file);
	fseek(p_file, 0, SEEK_SET);

	*cnt = (int) (size / sizeof(V3d));
	auto data = new V3d[size / sizeof(V3d)];
	size_t r;
	char* dst = (char*)(data);
	auto rem = size;
	while (rem > 0) {
		r = fread_s(dst, rem, (size_t)1, rem, p_file);
		if (!r) return nullptr;
		rem -= r;
		dst = dst + r;
	}

	std::cout << "loaded " << *cnt << " points" << std::endl;
	return data;
}

int main()
{
	LARGE_INTEGER frequency;
	if (::QueryPerformanceFrequency(&frequency) == FALSE)
		throw "foo";



	auto dataCount = 0;
	auto queryCount = 0;
	auto data = readV3ds("C:\\Users\\Schorsch\\Desktop\\grid.bin", &dataCount);
	auto query = readV3ds("C:\\Users\\Schorsch\\Desktop\\line.bin", &queryCount);

	LARGE_INTEGER start;
	if (::QueryPerformanceCounter(&start) == FALSE)
		throw "foo";

	auto a = new PointRKdTreeD(dataCount, data, 1E-6);
	
	LARGE_INTEGER end;
	if (::QueryPerformanceCounter(&end) == FALSE)
		throw "foo";

	double interval = static_cast<double>(end.QuadPart - start.QuadPart) / frequency.QuadPart;
	std::cout << "built tree (" <<  interval << "s)" << std::endl;


	for (int q = 0; q < 50; q++) {
		if (::QueryPerformanceCounter(&start) == FALSE)
			throw "foo";

		for (int i = 0; i < queryCount; i++) {
			auto q = ClosestToPointQuery(query[i]);
			a->GetClosest(q, 0);
			//std::cout << i << ": " << q.ClosestIndex << " (" << q.ClosestDist << ")" << std::endl;
		}

		if (::QueryPerformanceCounter(&end) == FALSE)
			throw "foo";

		interval = static_cast<double>(end.QuadPart - start.QuadPart) / frequency.QuadPart;
		std::cout << "query  (" << 1000000.0 * interval / (double)queryCount << "us)" << std::endl;
	}

	return 0; 
}

// Run program: Ctrl + F5 or Debug > Start Without Debugging menu
// Debug program: F5 or Debug > Start Debugging menu

// Tips for Getting Started: 
//   1. Use the Solution Explorer window to add/manage files
//   2. Use the Team Explorer window to connect to source control
//   3. Use the Output window to see build output and other messages
//   4. Use the Error List window to view errors
//   5. Go to Project > Add New Item to create new code files, or Project > Add Existing Item to add existing code files to the project
//   6. In the future, to open this project again, go to File > Open > Project and select the .sln file
