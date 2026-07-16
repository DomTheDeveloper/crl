#include <algorithm>
#include <array>
#include <atomic>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <functional>
#include <iomanip>
#include <iostream>
#include <map>
#include <numeric>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>
#include <omp.h>

namespace {
struct Point { int x{}, y{}; };
struct LineKey {
    int a{}, b{}, c{};
    bool operator<(LineKey const& o) const noexcept { return std::tie(a,b,c) < std::tie(o.a,o.b,o.c); }
};
struct Instance {
    int n{}, parity{};
    std::vector<Point> points;
    std::vector<std::vector<int>> lines;
    std::vector<std::vector<int>> incident;
    std::vector<int> pair_line;
    std::map<std::pair<int,int>,int> index;
};

LineKey line_key(Point const& p, Point const& q) {
    int dx=q.x-p.x, dy=q.y-p.y;
    int g=std::gcd(std::abs(dx),std::abs(dy)); dx/=g; dy/=g;
    if(dx<0 || (dx==0 && dy<0)){dx=-dx;dy=-dy;}
    int a=dy,b=-dx,c=-(a*p.x+b*p.y);
    return {a,b,c};
}
Instance build_instance(int n,int parity){
    Instance I; I.n=n; I.parity=parity;
    for(int y=0;y<n;y++) for(int x=0;x<n;x++) if(((x+y)&1)==parity){
        I.index[{x,y}]=(int)I.points.size(); I.points.push_back({x,y});
    }
    std::map<LineKey,std::set<int>> tmp;
    int N=I.points.size();
    for(int i=0;i<N;i++) for(int j=i+1;j<N;j++){
        auto &s=tmp[line_key(I.points[i],I.points[j])];s.insert(i);s.insert(j);
    }
    std::map<LineKey,int> lid;
    for(auto const& [k,s]:tmp) if(s.size()>=3){lid[k]=I.lines.size();I.lines.emplace_back(s.begin(),s.end());}
    I.incident.assign(N,{});
    for(int l=0;l<(int)I.lines.size();l++) for(int p:I.lines[l]) I.incident[p].push_back(l);
    I.pair_line.assign(N*N,-1);
    for(int i=0;i<N;i++) for(int j=i+1;j<N;j++){
        auto it=lid.find(line_key(I.points[i],I.points[j]));
        if(it!=lid.end()) I.pair_line[i*N+j]=I.pair_line[j*N+i]=it->second;
    }
    return I;
}

std::vector<int> read_seed(Instance const& I,std::string const& path){
    std::ifstream in(path); if(!in) throw std::runtime_error("cannot open seed: "+path);
    std::vector<int> out; std::string line;
    while(std::getline(in,line)){
        auto pos=line.find('#'); if(pos!=std::string::npos) line.resize(pos);
        std::istringstream ss(line); int x,y; if(!(ss>>x>>y)) continue;
        auto it=I.index.find({x,y}); if(it==I.index.end()) throw std::runtime_error("seed point outside parity board");
        out.push_back(it->second);
    }
    std::sort(out.begin(),out.end());
    if(std::adjacent_find(out.begin(),out.end())!=out.end()) throw std::runtime_error("duplicate seed point");
    return out;
}

bool verify(Instance const& I,std::vector<int> const& s,std::string* why=nullptr){
    for(size_t i=0;i<s.size();i++) for(size_t j=i+1;j<s.size();j++) for(size_t k=j+1;k<s.size();k++){
        auto a=I.points[s[i]],b=I.points[s[j]],c=I.points[s[k]];
        long long det=1LL*(b.x-a.x)*(c.y-a.y)-1LL*(b.y-a.y)*(c.x-a.x);
        if(det==0){if(why){std::ostringstream o;o<<"collinear ("<<a.x<<','<<a.y<<") ("<<b.x<<','<<b.y<<") ("<<c.x<<','<<c.y<<')';*why=o.str();}return false;}
    }
    return true;
}
void write_witness(Instance const& I,std::vector<int> s,std::string const& path,int destroy){
    std::sort(s.begin(),s.end(),[&](int a,int b){return std::tie(I.points[a].y,I.points[a].x)<std::tie(I.points[b].y,I.points[b].x);});
    std::ofstream out(path); if(!out) throw std::runtime_error("cannot write witness");
    out<<"# exact augmentation witness\n# n="<<I.n<<" parity="<<I.parity<<" size="<<s.size()<<" destroy="<<destroy<<"\n";
    for(int p:s) out<<I.points[p].x<<' '<<I.points[p].y<<'\n';
}

struct Stats { std::uint64_t dfs_nodes=0, leaves=0, removals=0, candidate_sum=0; };

struct RepairSearch {
    Instance const& I;
    int need;
    std::vector<int> count;
    std::vector<int> chosen;
    std::atomic<bool>& found;
    Stats stats;

    RepairSearch(Instance const& inst,int r,std::atomic<bool>& f):I(inst),need(r),count(inst.lines.size(),0),found(f){}
    bool legal(int p) const { for(int l:I.incident[p]) if(count[l]>=2) return false; return true; }
    void add(int p){for(int l:I.incident[p]) ++count[l];chosen.push_back(p);}
    void remove(int p){chosen.pop_back();for(int l:I.incident[p]) --count[l];}

    bool pair_compatible(int a, int b) const {
        const int n = static_cast<int>(I.points.size());
        const int line = I.pair_line[a * n + b];
        return line < 0 || count[line] == 0;
    }

    int clique_color_bound(std::vector<int> const& cand, int start) const {
        std::vector<int> avail;
        for(int i=start;i<(int)cand.size();++i) if(legal(cand[i])) avail.push_back(cand[i]);
        // A descending-degree order usually gives a tighter greedy coloring.
        std::vector<std::pair<int,int>> degree_point;
        degree_point.reserve(avail.size());
        for(int p:avail){
            int degree=0;
            for(int q:avail) if(q!=p && pair_compatible(p,q)) ++degree;
            degree_point.push_back({-degree,p});
        }
        std::stable_sort(degree_point.begin(), degree_point.end());
        for(std::size_t i=0;i<avail.size();++i) avail[i]=degree_point[i].second;
        std::vector<std::vector<int>> color_classes;
        for(int p:avail){
            bool placed=false;
            for(auto& cls:color_classes){
                bool adjacent=false;
                for(int q:cls) if(pair_compatible(p,q)){adjacent=true;break;}
                if(!adjacent){cls.push_back(p);placed=true;break;}
            }
            if(!placed) color_classes.push_back({p});
        }
        return static_cast<int>(color_classes.size());
    }

    bool dfs(std::vector<int> const& cand,int start,int left){
        ++stats.dfs_nodes;
        if(found.load(std::memory_order_relaxed)) return false;
        if(left==0){++stats.leaves;return true;}
        int available=0;
        for(int i=start;i<(int)cand.size();i++) if(legal(cand[i])) ++available;
        if(available<left) return false;
        if(left>=3 && available>left && clique_color_bound(cand,start)<left) return false;

        // Branch on legal candidates in deterministic order. Dynamic legality enforces every line capacity exactly.
        for(int i=start;i<(int)cand.size();i++){
            if((int)cand.size()-i<left) break;
            int p=cand[i]; if(!legal(p)) continue;
            add(p);
            if(dfs(cand,i+1,left-1)) return true;
            remove(p);
            if(found.load(std::memory_order_relaxed)) return false;
        }
        return false;
    }
};

std::uint64_t binom(int n,int k){
    if(k<0||k>n) return 0;
    k=std::min(k,n-k);
    __uint128_t v=1;
    for(int i=1;i<=k;i++) v=v*(n-k+i)/i;
    if(v>UINT64_MAX) throw std::runtime_error("combination count overflow");
    return static_cast<std::uint64_t>(v);
}

struct Options{
    int n=22,parity=0,destroy=5,threads=0;
    std::string seed,output="dmono22_augmented.txt";
    bool quiet=false;
    bool repair=false;
};
Options parse(int argc,char**argv){
    Options o; auto need=[&](int&i){if(++i>=argc)throw std::runtime_error("missing option value");return std::string(argv[i]);};
    for(int i=1;i<argc;i++){
        std::string a=argv[i];
        if(a=="--n")o.n=std::stoi(need(i)); else if(a=="--parity")o.parity=std::stoi(need(i));
        else if(a=="--seed")o.seed=need(i); else if(a=="--destroy")o.destroy=std::stoi(need(i));
        else if(a=="--threads")o.threads=std::stoi(need(i)); else if(a=="--output")o.output=need(i);
        else if(a=="--repair")o.repair=true;
        else if(a=="--quiet")o.quiet=true; else if(a=="--help"||a=="-h"){
            std::cout<<"usage: "<<argv[0]<<" --seed FILE [--destroy D] [--repair] [--threads T] [--output FILE]\n";std::exit(0);
        } else throw std::runtime_error("unknown option: "+a);
    }
    if(o.seed.empty())throw std::runtime_error("--seed is required");
    if(o.destroy<0)throw std::runtime_error("destroy must be nonnegative");
    return o;
}

} // namespace

int main(int argc,char**argv){
    try{
        Options o=parse(argc,argv); if(o.threads>0)omp_set_num_threads(o.threads);
        Instance I=build_instance(o.n,o.parity); auto seed=read_seed(I,o.seed);
        std::string why;
        std::vector<std::array<int,3>> initial_conflicts;
        for(int i=0;i<(int)seed.size();++i) for(int j=i+1;j<(int)seed.size();++j) for(int k=j+1;k<(int)seed.size();++k){
            auto a=I.points[seed[i]], b=I.points[seed[j]], c=I.points[seed[k]];
            long long det=1LL*(b.x-a.x)*(c.y-a.y)-1LL*(b.y-a.y)*(c.x-a.x);
            if(det==0) initial_conflicts.push_back({i,j,k});
        }
        if(!o.repair && !initial_conflicts.empty()) throw std::runtime_error("augmentation seed is not NTIL; use --repair for a near configuration");
        if(o.repair && initial_conflicts.empty()) throw std::runtime_error("--repair seed already has no collinear triple");
        if(o.destroy>(int)seed.size())throw std::runtime_error("destroy exceeds seed size");
        int target=o.repair ? (int)seed.size() : (int)seed.size()+1;
        int add_need=o.repair ? o.destroy : o.destroy+1;
        int K=seed.size();
        std::uint64_t total=binom(K,o.destroy);
        std::cout<<"instance n="<<o.n<<" parity="<<o.parity<<" points="<<I.points.size()
                 <<" lines="<<I.lines.size()<<" seed_size="<<K<<" target="<<target
                 <<" mode="<<(o.repair?"repair":"augment")<<" initial_conflicts="<<initial_conflicts.size()
                 <<" destroy="<<o.destroy<<" removal_subsets="<<total
                 <<" threads="<<omp_get_max_threads()<<'\n';

        std::atomic<bool> found(false); std::atomic<std::uint64_t> completed(0),eligible(0),nodes(0),leaves(0),candidate_sum(0);
        std::vector<int> answer; std::vector<int> answer_removed,answer_added;
        auto start=std::chrono::steady_clock::now();

        // d=0 is a single special branch; otherwise split exhaustively by the first removed seed position.
        int first_max = o.destroy==0 ? 1 : K-o.destroy+1;
        #pragma omp parallel for schedule(dynamic,1)
        for(int first=0;first<first_max;first++){
            if(found.load(std::memory_order_relaxed)) continue;
            std::vector<int> rem_pos;
            if(o.destroy>0)rem_pos.push_back(first);
            std::function<void(int,int)> enumerate;
            enumerate=[&](int next,int left){
                if(found.load(std::memory_order_relaxed))return;
                if(left>0){
                    for(int j=next;j<=K-left;j++){
                        rem_pos.push_back(j); enumerate(j+1,left-1); rem_pos.pop_back();
                        if(found.load(std::memory_order_relaxed))return;
                    }
                    return;
                }
                std::vector<unsigned char> removed(K,0),inbase(I.points.size(),0);
                for(int r:rem_pos)removed[r]=1;
                bool repair_eligible=true;
                if(o.repair){
                    for(auto const& t:initial_conflicts){
                        if(!removed[t[0]] && !removed[t[1]] && !removed[t[2]]) { repair_eligible=false; break; }
                    }
                }
                if(!repair_eligible){
                    completed.fetch_add(1,std::memory_order_relaxed);
                    return;
                }
                eligible.fetch_add(1,std::memory_order_relaxed);
                std::vector<int> base;base.reserve(K-o.destroy);
                for(int i=0;i<K;i++)if(!removed[i]){base.push_back(seed[i]);inbase[seed[i]]=1;}
                RepairSearch rs(I,add_need,found);
                for(int p:base)for(int l:I.incident[p])++rs.count[l];
                std::vector<int> cand;cand.reserve(I.points.size()-base.size());
                for(int p=0;p<(int)I.points.size();p++)if(!inbase[p]&&rs.legal(p))cand.push_back(p);
                // Most constrained candidates first; order remains deterministic and completeness-preserving.
                std::stable_sort(cand.begin(),cand.end(),[&](int a,int b){
                    int sa=0,sb=0;for(int l:I.incident[a])sa+=rs.count[l];for(int l:I.incident[b])sb+=rs.count[l];
                    return sa>sb;
                });
                rs.stats.candidate_sum+=cand.size();
                bool hit=(int)cand.size()>=add_need && rs.dfs(cand,0,add_need);
                nodes.fetch_add(rs.stats.dfs_nodes,std::memory_order_relaxed);
                leaves.fetch_add(rs.stats.leaves,std::memory_order_relaxed);
                candidate_sum.fetch_add(cand.size(),std::memory_order_relaxed);
                auto done=completed.fetch_add(1,std::memory_order_relaxed)+1;
                if(hit){
                    std::vector<int> final=base;final.insert(final.end(),rs.chosen.begin(),rs.chosen.end());
                    std::string reason;
                    if((int)final.size()!=target||!verify(I,final,&reason)) {
                        #pragma omp critical(io)
                        std::cerr << "INTERNAL ERROR: repair candidate failed verification: " << reason << '\n';
                        std::abort();
                    }
                    bool expected=false;
                    if(found.compare_exchange_strong(expected,true,std::memory_order_acq_rel)){
                        #pragma omp critical(answer)
                        {answer=std::move(final);for(int r:rem_pos)answer_removed.push_back(seed[r]);answer_added=rs.chosen;}
                    }
                }
                if(!o.quiet && (done%10000==0 || done==total)){
                    #pragma omp critical(io)
                    {auto now=std::chrono::steady_clock::now();double sec=std::chrono::duration<double>(now-start).count();
                    std::cerr<<"completed="<<done<<'/'<<total<<" dfs_nodes="<<nodes.load()<<" rate="
                             <<std::fixed<<std::setprecision(1)<<(sec?done/sec:0)<<" removals/s\n";}
                }
            };
            enumerate(o.destroy==0?0:first+1,o.destroy==0?0:o.destroy-1);
        }
        auto end=std::chrono::steady_clock::now();double sec=std::chrono::duration<double>(end-start).count();
        if(found.load(std::memory_order_acquire)){
            write_witness(I,answer,o.output,o.destroy);
            std::cout<<"SAT exact_"<<(o.repair?"repair":"augmentation")<<" destroy="<<o.destroy<<" completed_before_hit="<<completed.load()
                     <<" dfs_nodes="<<nodes.load()<<" elapsed_seconds="<<std::fixed<<std::setprecision(3)<<sec
                     <<" output="<<o.output<<'\n';
            std::cout<<"removed";for(int p:answer_removed)std::cout<<" ("<<I.points[p].x<<','<<I.points[p].y<<')';std::cout<<"\nadded";
            for(int p:answer_added) std::cout<<" ("<<I.points[p].x<<','<<I.points[p].y<<')';
            std::cout<<'\n';
            return 0;
        }
        if(completed.load()!=total)throw std::runtime_error("incomplete enumeration without witness");
        std::cout<<"UNSAT_NEIGHBORHOOD mode="<<(o.repair?"repair":"augment")<<" destroy="<<o.destroy<<" completed_removal_subsets="<<completed.load()
                 <<" eligible_removal_subsets="<<eligible.load()<<" dfs_nodes="<<nodes.load()<<" terminal_addition_sets="<<leaves.load()
                 <<" average_initial_candidates="<<std::fixed<<std::setprecision(3)
                 <<(total?double(candidate_sum.load())/double(total):0.0)
                 <<" elapsed_seconds="<<std::setprecision(3)<<sec<<'\n';
        std::cout<<"NOTE this excludes only configurations obtainable from the supplied seed by removing exactly "
                 <<o.destroy<<" seed points and adding exactly "<<add_need<<" points; it is not a global UNSAT proof.\n";
        return 2;
    }catch(std::exception const&e){std::cerr<<"error: "<<e.what()<<'\n';return 1;}
}
