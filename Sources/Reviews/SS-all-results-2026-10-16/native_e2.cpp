#include "algebras/dbAdamsSS.h"
#include "algebras/groebner.h"
#include "json.h"
#include <sqlite3.h>
#include <fstream>
#include <memory>
#include <map>
using namespace alg2; using nlohmann::json; using namespace myio;
const std::string root="/tmp/SS-All-Results-Audit-20261016/";
json config,maps; std::map<std::string,json> specs; std::map<std::string,bool> isring;
std::vector<std::vector<std::string>> query(std::string path,std::string sql){
 sqlite3* db=nullptr; if(sqlite3_open_v2(path.c_str(),&db,SQLITE_OPEN_READONLY,nullptr)!=SQLITE_OK)throw std::runtime_error("open "+path);
 sqlite3_stmt* stmt=nullptr; if(sqlite3_prepare_v2(db,sql.c_str(),-1,&stmt,nullptr)!=SQLITE_OK)throw std::runtime_error(sql);
 std::vector<std::vector<std::string>> out;
 while(sqlite3_step(stmt)==SQLITE_ROW){std::vector<std::string> row; for(int i=0;i<sqlite3_column_count(stmt);++i){const auto* txt=sqlite3_column_text(stmt,i); row.push_back(txt?(const char*)txt:"");}out.push_back(row);}
 sqlite3_finalize(stmt);sqlite3_close(db);return out;
}
struct Spectrum {bool ring; std::unique_ptr<Groebner> rgb; std::unique_ptr<GroebnerMod> mgb; BasisMon rbasis; BasisMMod mbasis;};
std::map<std::string,std::unique_ptr<Spectrum>> spectra;
Spectrum& getsp(std::string n){
 if(spectra.count(n))return *spectra.at(n);
 auto p=std::make_unique<Spectrum>(); p->ring=isring[n]; auto spec=specs[n]; std::string path=root+"full-inputs/kervaire-49/"+spec.at("path").get<std::string>(), prefix=n+"_AdamsE2";
 if(p->ring){Poly1d rels;for(auto& row:query(path,"SELECT rel FROM "+prefix+"_relations ORDER BY t"))rels.push_back(Deserialize<Poly>(row[0]));p->rgb=std::make_unique<Groebner>(DEG_MAX,int1d{},std::move(rels)); for(auto& row:query(path,"SELECT s,t,mon FROM "+prefix+"_basis ORDER BY id"))p->rbasis[{std::stoi(row[0]),std::stoi(row[1])}].push_back(Deserialize<Mon>(row[2]));}
 else{Mod1d rels;for(auto& row:query(path,"SELECT rel FROM "+prefix+"_relations ORDER BY t"))rels.push_back(Deserialize<Mod>(row[0]));auto& parent=getsp(spec.at("over"));p->mgb=std::make_unique<GroebnerMod>(parent.rgb.get(),DEG_MAX,int1d{},std::move(rels));for(auto& row:query(path,"SELECT s,t,mon FROM "+prefix+"_basis ORDER BY id"))p->mbasis[{std::stoi(row[0]),std::stoi(row[1])}].push_back(Deserialize<MMod>(row[2]));}
 auto& result=*p; spectra[n]=std::move(p);return result;
}
std::map<int,Poly1d> images_poly;std::map<int,Mod1d> images_mod;
void loadimages(int ordinal){auto m=maps.at(ordinal);std::string path=root+"full-inputs/kervaire-49/"+m.at("path").get<std::string>();auto tables=query(path,"SELECT name FROM sqlite_master WHERE type='table' AND name LIKE 'map_AdamsE2_%'");if(tables.size()!=1)throw std::runtime_error("maptable");auto rows=query(path,"SELECT map FROM "+tables[0][0]+" ORDER BY id");if(isring[m.at("to")]){auto& arr=images_poly[ordinal];for(auto& row:rows)arr.push_back(Deserialize<Poly>(row[0]));}else{auto& arr=images_mod[ordinal];for(auto& row:rows)arr.push_back(Deserialize<Mod>(row[0]));}}
std::pair<AdamsDeg,int1d> evaluate(int ordinal,AdamsDeg d,const int1d& x){
 auto m=maps.at(ordinal); std::string from=m.at("from"),to=m.at("to"),kind=m.at("kind"); auto target=d+AdamsDeg(m.at("AF"),m.at("deg_t"));
 if(x.empty())return {target,{}};
 if(kind=="composition"){auto y=x;for(auto child:m.at("resolved_children")){auto next=evaluate(child,d,y);d=next.first;y=next.second;}if(d.s!=target.s||d.t!=target.t)throw std::runtime_error("compositiondegree");return {d,y};}
 auto& src=getsp(from);auto& dst=getsp(to);
 if(kind=="factor"){
  auto f=m.at("factor");int stem=f[0],s=f[1];int1d inds=f[2].is_number()?int1d{f[2].get<int>()}:f[2].get<int1d>();AdamsDeg df(s,stem+s);
  if(src.ring){auto xp=Indices2Poly(x,src.rbasis.at(d)); if(dst.ring){auto fp=Indices2Poly(inds,dst.rbasis.at(df));auto yp=dst.rgb->Reduce(xp*fp);return {target,yp?Poly2Indices(yp,dst.rbasis.at(target)):int1d{}};}else{auto fp=Indices2Mod(inds,dst.mbasis.at(df));auto yp=dst.mgb->Reduce(xp*fp);return {target,yp?Mod2Indices(yp,dst.mbasis.at(target)):int1d{}};}}
  else{auto& parent=getsp(specs[from].at("over"));auto xp=Indices2Mod(x,src.mbasis.at(d));auto fp=Indices2Poly(inds,parent.rbasis.at(df));auto yp=dst.mgb->Reduce(fp*xp);return {target,yp?Mod2Indices(yp,dst.mbasis.at(target)):int1d{}};}
 }
 if(m.contains("over"))throw std::runtime_error("unsupported nonidentity scalar");
 if(!images_poly.count(ordinal)&&!images_mod.count(ordinal))loadimages(ordinal);
 if(src.ring){auto xp=Indices2Poly(x,src.rbasis.at(d));auto yp=dst.rgb->Reduce(subs(xp,images_poly[ordinal]));return {target,yp?Poly2Indices(yp,dst.rbasis.at(target)):int1d{}};}
 auto xp=Indices2Mod(x,src.mbasis.at(d));if(dst.ring){auto yp=dst.rgb->Reduce(subs(xp,images_poly[ordinal]));return {target,yp?Poly2Indices(yp,dst.rbasis.at(target)):int1d{}};}auto yp=dst.mgb->Reduce(subs(xp,images_mod[ordinal]));return {target,yp?Mod2Indices(yp,dst.mbasis.at(target)):int1d{}};
}
int main(int argc,char** argv){
 std::ifstream(root+"full-inputs/kervaire-49/ss.json")>>config;std::ifstream(root+"input-map-decoding.json")>>maps;
 for(auto section:{"rings","modules"})for(auto spec:config.at(section)){std::string n=spec.at("name");specs[n]=spec;isring[n]=(std::string(section)=="rings");}
 std::map<std::string,int> first;for(auto m:maps)first.emplace(m.at("name"),m.at("ordinal"));json rows;std::ifstream(argc>1?argv[1]:root+"logs-full-synthetic-rows.json")>>rows;json out=json::array();int count=0,m0=0,m1=0,fail=0;
 for(auto row:rows){if(argc<=1 && row.at("reason")!="SynCs")continue;int id=row.at("id");try{AdamsDeg d(row.at("s"),row.at("t"));auto x=row.at("x").is_string()?Deserialize<int1d>(row.at("x")):row.at("x").get<int1d>();auto result=evaluate(first.at(row.at("map")),d,x);std::string branch=result.second.empty()?"M0":"M1";if(branch=="M0")++m0;else ++m1;out.push_back({{"id",id},{"target_degree",{result.first.s,result.first.t}},{"E2_image",result.second},{"branch",branch}});}catch(const std::exception& e){++fail;out.push_back({{"id",id},{"error",e.what()}});}if(++count%100==0)std::cerr<<count<<" M0="<<m0<<" M1="<<m1<<" failed="<<fail<<std::endl;}
 json result={{"summary",{{"rows",count},{"M0",m0},{"M1",m1},{"failed",fail},{"method","original official C++ Deserialize/Indices2Poly/Mod/subs/Groebner::Reduce/Poly2Indices with SQL read-only and official ORDER BY"}}},{"rows",out}};std::ofstream(argc>2?argv[2]:root+"native-E2-classification.json")<<result.dump(2)<<'\n';std::cout<<result.at("summary").dump()<<std::endl;
}
