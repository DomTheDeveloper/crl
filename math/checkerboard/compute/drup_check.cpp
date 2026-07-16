#include <algorithm>
#include <cctype>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
#include <unordered_map>
using namespace std;
struct Clause { vector<int> lits; int w0=0,w1=1; bool active=true; };
struct VecHash { size_t operator()(vector<int> const& v) const noexcept { uint64_t h=1469598103934665603ULL; for(int x:v){h^=(uint32_t)x;h*=1099511628211ULL;} return (size_t)h; } };
struct Checker {
 int nvars; vector<int8_t> val; vector<int> trail; size_t qhead=0,root_size=0; bool root_conflict=false;
 vector<Clause> clauses; vector<vector<int>> watches; unordered_map<vector<int>,vector<int>,VecHash> clause_ids;
 uint64_t propagations=0,rup_checks=0,added=0,skipped_sat=0,units=0;
 explicit Checker(int n):nvars(n),val(n+1,0),watches(2*(n+1)){}
 void ensure(int v){if(v<=nvars)return;nvars=v;val.resize(nvars+1,0);watches.resize(2*(nvars+1));}
 int idx(int lit)const{return 2*abs(lit)+(lit<0);} int litval(int lit)const{int8_t x=val[abs(lit)];if(!x)return 0;return lit>0?x:-x;}
 bool assign_lit(int lit){int v=abs(lit);ensure(v);int8_t want=lit>0?1:-1;if(val[v])return val[v]==want;val[v]=want;trail.push_back(lit);return true;}
 bool propagate(){while(qhead<trail.size()){int false_lit=-trail[qhead++];auto &ws=watches[idx(false_lit)];size_t out=0;for(size_t ii=0;ii<ws.size();++ii){int cid=ws[ii];Clause &c=clauses[cid];if(!c.active)continue;int fp=-1,op=-1;if(c.lits[c.w0]==false_lit){fp=c.w0;op=c.w1;}else if(c.lits[c.w1]==false_lit){fp=c.w1;op=c.w0;}else continue;int other=c.lits[op];if(litval(other)==1){ws[out++]=cid;continue;}int repl=-1;for(int k=0;k<(int)c.lits.size();++k){if(k==c.w0||k==c.w1)continue;if(litval(c.lits[k])!=-1){repl=k;break;}}if(repl>=0){if(fp==c.w0)c.w0=repl;else c.w1=repl;watches[idx(c.lits[repl])].push_back(cid);}else{ws[out++]=cid;int ov=litval(other);if(ov==-1){for(size_t jj=ii+1;jj<ws.size();++jj)ws[out++]=ws[jj];ws.resize(out);return false;}if(ov==0&&!assign_lit(other)){for(size_t jj=ii+1;jj<ws.size();++jj)ws[out++]=ws[jj];ws.resize(out);return false;}}++propagations;}ws.resize(out);}return true;}
 bool normalize(vector<int>&c){for(int x:c)ensure(abs(x));sort(c.begin(),c.end(),[](int a,int b){if(abs(a)!=abs(b))return abs(a)<abs(b);return a<b;});vector<int>d;d.reserve(c.size());for(int x:c){if(!d.empty()&&x==d.back())continue;if(!d.empty()&&x==-d.back())return true;d.push_back(x);}c.swap(d);return false;}
 bool add_formula_clause(vector<int>c){if(normalize(c)){++skipped_sat;return true;}vector<int>raw=c;if(root_conflict)return true;vector<int>d;for(int lit:c){int x=litval(lit);if(x==1){++skipped_sat;return true;}if(x==0)d.push_back(lit);}if(d.empty()){root_conflict=true;return false;}if(d.size()==1){++units;if(!assign_lit(d[0])||!propagate()){root_conflict=true;return false;}root_size=trail.size();qhead=root_size;return true;}int cid=clauses.size();clauses.push_back({move(d),0,1,true});clause_ids[raw].push_back(cid);watches[idx(clauses[cid].lits[0])].push_back(cid);watches[idx(clauses[cid].lits[1])].push_back(cid);++added;return true;}
 void delete_clause(vector<int>c){if(normalize(c))return;auto it=clause_ids.find(c);if(it==clause_ids.end())return;for(int cid:it->second)clauses[cid].active=false;clause_ids.erase(it);}
 bool check_rup(vector<int>c){++rup_checks;if(root_conflict)return true;if(normalize(c))return true;size_t save=root_size;bool conflict=false;for(int lit:c){if(!assign_lit(-lit)){conflict=true;break;}}if(!conflict&&!propagate())conflict=true;for(size_t i=trail.size();i>save;--i)val[abs(trail[i-1])]=0;trail.resize(save);qhead=save;return conflict;}
};
static bool parse_line(const string&line,vector<int>&lits,bool&deletion){lits.clear();deletion=false;size_t p=0;while(p<line.size()&&isspace((unsigned char)line[p]))++p;if(p==line.size()||line[p]=='c'||line[p]=='p')return false;if(line[p]=='d'){deletion=true;++p;}const char*s=line.c_str()+p;char*e;while(*s){while(*s&&isspace((unsigned char)*s))++s;if(!*s)break;long x=strtol(s,&e,10);if(e==s)break;s=e;if(x==0)break;lits.push_back((int)x);}return true;}
static long load_clauses(istream&in,Checker&ck){string line;vector<int>lits;bool del;long read=0;while(getline(in,line))if(parse_line(line,lits,del)&&!del){ck.add_formula_clause(lits);++read;}return read;}
int main(int argc,char**argv){if(argc!=3&&argc!=4){cerr<<"usage: drup_check input.cnf proof.drup [extra_units.cnf]\n";return 2;}ifstream in(argv[1]);if(!in){cerr<<"cannot open cnf\n";return 2;}string line;int nv=0;long declared=0;while(getline(in,line)){if(line.rfind("p cnf",0)==0){istringstream ss(line);string p,cnf;ss>>p>>cnf>>nv>>declared;break;}}if(!nv){cerr<<"missing header\n";return 2;}Checker ck(nv);long read=load_clauses(in,ck);if(argc==4){ifstream ex(argv[3]);if(!ex){cerr<<"cannot open extra clauses\n";return 2;}read+=load_clauses(ex,ck);}cerr<<"c loaded "<<read<<" clauses, root assignments "<<ck.root_size<<"\n";ifstream pf(argv[2]);if(!pf){cerr<<"cannot open proof\n";return 2;}vector<int>lits;bool del;uint64_t lines=0,adds=0,dels=0;bool saw_empty=false;while(getline(pf,line)){++lines;if(!parse_line(line,lits,del))continue;if(del){++dels;ck.delete_clause(lits);continue;}++adds;if(!ck.check_rup(lits)){cerr<<"s INVALID: non-RUP addition at proof line "<<lines<<" (addition "<<adds<<") size "<<lits.size()<<"\n";return 1;}if(lits.empty())saw_empty=true;ck.add_formula_clause(lits);if(adds%100000==0)cerr<<"c checked "<<adds<<" additions, root "<<ck.root_size<<", clauses "<<ck.clauses.size()<<"\n";}if(!saw_empty){cerr<<"s INVALID: no empty clause\n";return 1;}cout<<"s VERIFIED\n";cout<<"c additions "<<adds<<" deletions_applied "<<dels<<" proof_lines "<<lines<<"\n";cout<<"c rup_checks "<<ck.rup_checks<<" stored_clauses "<<ck.clauses.size()<<" root_assignments "<<ck.root_size<<"\n";return 0;}
