#include <bits/stdc++.h>

using namespace std;

string ltrim(const string &);
string rtrim(const string &);

/*
 * Complete the 'pack_squares' function below.
 *
 * The function is expected to return a 2D_INTEGER_ARRAY.
 * The function accepts INTEGER_ARRAY squares as parameter.
 */

// X grows downward (rows), Y grows rightward (columns).
// Squares are packed in a strip of width W along Y, growing down along X.

namespace packer {

using Clock = chrono::steady_clock;
static Clock::time_point T0;
static const double TIME_LIMIT = 1.6;  // seconds per call

static double elapsed() {
    return chrono::duration<double>(Clock::now() - T0).count();
}

struct Seg {
    int y, w, h;  // start column, width, height of this skyline piece
};

static int n, m;
static long long S;
static vector<int> D;               // distinct sizes, ascending
static vector<vector<int>> groups;  // square indices for each distinct size

struct State {
    vector<int> act;  // distinct-size indices still available, ascending
    vector<int> cnt;  // remaining count per distinct size
    vector<pair<int, int>> pos;
    vector<Seg> segs;
    int placed = 0, maxh = 0;
};

static State initState(int W) {
    State st;
    st.cnt.resize(D.size());
    for (size_t k = 0; k < D.size(); k++) {
        st.act.push_back((int)k);
        st.cnt[k] = (int)groups[k].size();
    }
    st.pos.assign(n, {0, 0});
    st.segs.push_back({0, W, 0});
    return st;
}

static void mergeAround(vector<Seg> &segs, int bi) {
    int i = max(bi - 1, 0);
    while (i + 1 < (int)segs.size() && i <= bi + 1) {
        if (segs[i].h == segs[i + 1].h) {
            segs[i].w += segs[i + 1].w;
            segs.erase(segs.begin() + i + 1);
        } else {
            i++;
        }
    }
}

// Best-fit skyline: fill the lowest gap with the largest square that fits.
// Runs from st to completion; saves a copy into snap when snapAt squares are placed.
static int bestFit(State &st, int W, mt19937 *rng, double noise, int snapAt, State *snap) {
    auto rnd = [&]() { return (*rng)() / 4294967296.0; };
    vector<Seg> &segs = st.segs;
    while (st.placed < n) {
        if (snap && st.placed == snapAt) *snap = st;
        int bi = 0;
        for (int i = 1; i < (int)segs.size(); i++)
            if (segs[i].h < segs[bi].h) bi = i;
        int y0 = segs[bi].y, gw = segs[bi].w, gh = segs[bi].h;
        // largest available size <= gw
        int lo = 0, hi = (int)st.act.size();
        while (lo < hi) {
            int mid = (lo + hi) / 2;
            if (D[st.act[mid]] <= gw) lo = mid + 1; else hi = mid;
        }
        int k = lo - 1;
        if (k < 0) {
            int nh = INT_MAX;
            if (bi > 0) nh = min(nh, segs[bi - 1].h);
            if (bi + 1 < (int)segs.size()) nh = min(nh, segs[bi + 1].h);
            segs[bi].h = nh;
        } else {
            if (noise > 0 && k > 0 && rnd() < noise) {
                int a = max(0, k - 2);
                k = a + (int)((*rng)() % (unsigned)(k - a + 1));
            }
            int d = st.act[k];
            int s = D[d];
            int idx = groups[d][--st.cnt[d]];
            if (st.cnt[d] == 0) st.act.erase(st.act.begin() + k);
            st.placed++;
            int lh = bi > 0 ? segs[bi - 1].h : INT_MAX;
            int rh = bi + 1 < (int)segs.size() ? segs[bi + 1].h : INT_MAX;
            bool goLeft = (noise > 0 && rnd() < noise) ? rnd() < 0.5 : lh >= rh;
            int top = gh + s;
            st.maxh = max(st.maxh, top);
            if (s == gw) {
                segs[bi].h = top;
                st.pos[idx] = {gh, y0};
            } else if (goLeft) {
                st.pos[idx] = {gh, y0};
                segs[bi] = {y0 + s, gw - s, gh};
                segs.insert(segs.begin() + bi, Seg{y0, s, top});
            } else {
                st.pos[idx] = {gh, y0 + gw - s};
                segs[bi] = {y0, gw - s, gh};
                segs.insert(segs.begin() + bi + 1, Seg{y0 + gw - s, s, top});
            }
        }
        mergeAround(segs, bi);
    }
    return st.maxh;
}

// Backtracking fill of a W x H rectangle: always cover the lowest-leftmost
// free cell with a square or with waste, within the slack W*H - sum(a^2).
struct Exact {
    int W, H;
    vector<int> cnt;
    vector<pair<int, int>> pos;
    long long nodes = 0, budget;
    double deadline;
    bool stop = false;

    Exact(int W_, int H_, long long budget_, double deadline_)
        : W(W_), H(H_), budget(budget_), deadline(deadline_) {
        cnt.resize(D.size());
        for (size_t k = 0; k < D.size(); k++) cnt[k] = (int)groups[k].size();
        pos.assign(n, {0, 0});
    }

    bool rec(const vector<Seg> &segs, int remaining, long long slack) {
        if (remaining == 0) return true;
        if (++nodes > budget || ((nodes & 1023) == 0 && elapsed() > deadline)) stop = true;
        if (stop) return false;
        int bi = 0;
        for (int i = 1; i < (int)segs.size(); i++)
            if (segs[i].h < segs[bi].h) bi = i;
        int y0 = segs[bi].y, g = segs[bi].w, h = segs[bi].h;
        int lim = min(g, H - h);
        for (int k = (int)D.size() - 1; k >= 0; k--) {
            int s = D[k];
            if (s > lim || cnt[k] == 0) continue;
            cnt[k]--;
            vector<Seg> nxt(segs.begin(), segs.begin() + bi);
            if (s == g) {
                nxt.push_back({y0, g, h + s});
            } else {
                nxt.push_back({y0, s, h + s});
                nxt.push_back({y0 + s, g - s, h});
            }
            nxt.insert(nxt.end(), segs.begin() + bi + 1, segs.end());
            mergeAround(nxt, bi);
            if (rec(nxt, remaining - 1, slack)) {
                pos[groups[k][cnt[k]]] = {h, y0};
                cnt[k]++;
                return true;
            }
            cnt[k]++;
            if (stop) return false;
        }
        // leave the gap empty: raise it to its lower neighbour (or the top)
        int nh = INT_MAX;
        if (bi > 0) nh = min(nh, segs[bi - 1].h);
        if (bi + 1 < (int)segs.size()) nh = min(nh, segs[bi + 1].h);
        if (nh == INT_MAX) nh = H;
        long long cost = (long long)g * (nh - h);
        if (cost <= slack) {
            vector<Seg> nxt = segs;
            nxt[bi].h = nh;
            mergeAround(nxt, bi);
            return rec(nxt, remaining, slack - cost);
        }
        return false;
    }
};

}  // namespace packer

vector<vector<int>> pack_squares(vector<int> squares) {
    using namespace packer;
    T0 = Clock::now();
    n = (int)squares.size();
    if (n == 0) return {};
    m = *max_element(squares.begin(), squares.end());
    S = 0;
    long long sumSides = 0;
    for (int a : squares) {
        S += (long long)a * a;
        sumSides += a;
    }
    D.clear();
    groups.clear();
    {
        map<int, vector<int>> g;
        for (int i = 0; i < n; i++) g[squares[i]].push_back(i);
        for (auto &kv : g) {
            D.push_back(kv.first);
            groups.push_back(kv.second);
        }
    }

    // fallback: one column
    vector<pair<int, int>> bestPos(n);
    long long bestArea;
    {
        long long x = 0;
        for (int i = 0; i < n; i++) {
            bestPos[i] = {(int)x, 0};
            x += squares[i];
        }
        bestArea = x * m;
    }

    auto widthBound = [&](long long W) { return W * max<long long>(m, (S + W - 1) / W); };
    long long maxW = max<long long>(m, min<long long>(sumSides, (long long)(2 * sqrt((double)S)) + 2));
    long long L = LLONG_MAX;
    for (long long W = m; W <= maxW; W++) L = min(L, widthBound(W));

    // 1) deterministic best-fit over widths: narrow strips (2-4 times the
    //    largest side) pack best, so scan those first, then the rest
    vector<pair<long long, int>> tried;
    {
        vector<int> order;
        for (long long W = m; W <= maxW && W <= 4LL * m; W++) order.push_back((int)W);
        for (long long W = 4LL * m + 1; W <= maxW; W++) order.push_back((int)W);
        for (int W : order) {
            if (elapsed() > TIME_LIMIT * 0.25) break;
            State st = initState(W);
            long long a = (long long)W * bestFit(st, W, nullptr, 0, -1, nullptr);
            tried.push_back({a, W});
            if (a < bestArea) {
                bestArea = a;
                bestPos = st.pos;
            }
        }
    }
    auto result = [&]() {
        vector<vector<int>> out(n);
        for (int i = 0; i < n; i++) out[i] = {bestPos[i].first, bestPos[i].second};
        return out;
    };
    if (bestArea == L) return result();

    // 2) exact search over rectangles W x H (W <= H) in order of area,
    //    with growing node budgets; only worth it for smaller inputs
    if (n <= 200) {
        double exactDeadline = TIME_LIMIT * 0.5;
        long long budget = 20000;
        while (elapsed() < exactDeadline && bestArea > L) {
            vector<tuple<long long, int, int>> rects;
            for (long long W = m; W <= maxW; W++) {
                long long H = max<long long>(m, (S + W - 1) / W);
                if (W > H) continue;
                for (; W * H < bestArea; H++) rects.push_back({W * H, (int)W, (int)H});
            }
            if (rects.empty()) break;
            sort(rects.begin(), rects.end());
            bool improved = false;
            for (auto &[area, W, H] : rects) {
                if (area >= bestArea || elapsed() > exactDeadline) break;
                Exact ex(W, H, budget, exactDeadline);
                if (ex.rec({{0, W, 0}}, n, area - S)) {
                    bestArea = area;
                    bestPos = ex.pos;
                    improved = true;
                    break;
                }
            }
            if (!improved) {
                budget *= 4;
                if (budget > 2000000000LL) break;
            }
        }
    }

    // 3) randomized best-fit on the widths that packed best: full restarts
    //    plus restarts of only the tail, where most of the waste ends up
    mt19937 rng(12345);
    sort(tried.begin(), tried.end());
    struct Entry {
        int W;
        bool full;
        State snap;
    };
    vector<Entry> pool;
    for (size_t t = 0; t < tried.size() && t < 12; t++) {
        int W = tried[t].second;
        pool.push_back({W, true, State()});
        for (double frac : {0.5, 0.7, 0.85}) {
            int cut = (int)(n * frac);
            if (cut <= 0 || cut >= n) continue;
            State st = initState(W), snap;
            bestFit(st, W, nullptr, 0, cut, &snap);
            pool.push_back({W, false, snap});
        }
    }
    const double noises[] = {0.02, 0.05, 0.1, 0.2, 0.3};
    while (!pool.empty() && elapsed() < TIME_LIMIT && bestArea > L) {
        Entry &e = pool[rng() % pool.size()];
        if (widthBound(e.W) >= bestArea) continue;
        State st = e.full ? initState(e.W) : e.snap;
        long long a = (long long)e.W * bestFit(st, e.W, &rng, noises[rng() % 5], -1, nullptr);
        if (a < bestArea) {
            bestArea = a;
            bestPos = st.pos;
        }
    }

    return result();
}

int main()
{
    const char *outPath = getenv("OUTPUT_PATH");
    ofstream fileOut;
    if (outPath) fileOut.open(outPath);
    ostream &fout = outPath ? static_cast<ostream &>(fileOut) : cout;

    string squares_count_temp;
    getline(cin, squares_count_temp);

    int squares_count = stoi(ltrim(rtrim(squares_count_temp)));

    vector<int> squares(squares_count);

    for (int i = 0; i < squares_count; i++) {
        string squares_item_temp;
        getline(cin, squares_item_temp);

        int squares_item = stoi(ltrim(rtrim(squares_item_temp)));

        squares[i] = squares_item;
    }

    vector<vector<int>> result = pack_squares(squares);

    for (size_t i = 0; i < result.size(); i++) {
        for (size_t j = 0; j < result[i].size(); j++) {
            fout << result[i][j];

            if (j != result[i].size() - 1) {
                fout << " ";
            }
        }

        if (i != result.size() - 1) {
            fout << "\n";
        }
    }

    fout << "\n";

    if (outPath) fileOut.close();

    return 0;
}

string ltrim(const string &str) {
    string s(str);

    s.erase(
        s.begin(),
        find_if(s.begin(), s.end(), [](unsigned char c) { return !isspace(c); })
    );

    return s;
}

string rtrim(const string &str) {
    string s(str);

    s.erase(
        find_if(s.rbegin(), s.rend(), [](unsigned char c) { return !isspace(c); }).base(),
        s.end()
    );

    return s;
}
