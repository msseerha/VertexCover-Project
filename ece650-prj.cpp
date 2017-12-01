#include <iostream>
#include <sstream>
#include <vector>
#include <string>
#include <time.h>
#include <algorithm>
#include <pthread.h>
#include <unistd.h>
#include <errno.h>
#include <cmath>
#include <iterator>
#include <map>

#include <memory>
#include "minisat/core/SolverTypes.h"
#include "minisat/core/Solver.h"

#define Junk 1000
#define numb 100
#define ratio 10

#define handle_error(msg) \
    do { perror(msg); exit(EXIT_FAILURE); } while (0)

#define handle_error_en(en, msg) \
    do { errno = en; perror(msg); exit(EXIT_FAILURE); } while (0)

using namespace std;

//-----Global Variables

vector<int> eline;
int vcount;
clockid_t cid_app1,cid_app2,cid_sat;
struct timespec ts_app1,ts_app2,ts_sat;
long double time_sat,time_approx1,time_approx2;

pthread_t cnf_sat, approxer_1, approxer_2;

vector<int> vc; //cnf_sat
vector <int> newt;//approx1
vector <int> vertexCV;//approx2

bool calc_mode = false;
unsigned int one,two,three;
vector <long double> timer_cnf, timer_approx1, timer_approx2;
vector <float> store1,store2;

//////////////////////////////////////////////////////////////////

static long double pclock(clockid_t cid)
{
   struct timespec ts;

    if (clock_gettime(cid, &ts) == -1)
    {
		handle_error("clock_gettime");
    }

    return (ts.tv_sec*1000000)+(ts.tv_nsec/1000);
}

///////////////////////////////////////////////////////////////////

struct by_second
{
    template <typename Pair>
    bool operator()(const Pair& a, const Pair& b)
    {
        return a.second < b.second;
    }
};


template <typename Fwd>
typename map<typename iterator_traits<Fwd>::value_type, int>::value_type
VC_picker(Fwd begin, Fwd end)
{
    map<typename iterator_traits<Fwd>::value_type, int> count;

    for (Fwd it = begin; it != end; ++it)
        ++count[*it];

    return *max_element(count.begin(), count.end(), by_second());
}
///////////////////////////////////////////////////////////

vector<int> nutter (vector <int> nut,int no1, int no2 = Junk){

for (vector<int>::iterator it=nut.begin(); it!=nut.end();)
{
	if (no2==Junk)
	{
        if ((*it == no1) || (*(it+1) == no1))
        {
            it = nut.erase(it,it+2);
        } 
        else
        {
            ++it;
            ++it;
        }
    } 
    else
    {   
        if ((*it == no1) || (*(it+1) == no1)||(*it == no2) || (*(it+1) == no2))
        {
            it = nut.erase(it,it+2);
        } 
        else
        {
            ++it;
            ++it;
        }
    }
}
    return nut;
}

////////////////////////////////////////////////////////////////////

void* CNF_SAT(void* arg){

int vnumber=vcount;
int min=1,max=vnumber;
std::unique_ptr<Minisat::Solver> solver(new Minisat::Solver());
bool res;
int vcover;
vc.clear();

while(min<=max)
{   
	//Declaring---------------------------------------------------
	
    vcover=(min+max)/2;
	Minisat::vec<Minisat::Lit> clause;
	solver.reset (new Minisat::Solver());
	vector< vector<Minisat::Lit> > litero(vnumber,vector<Minisat::Lit>(vnumber));
    litero.clear();
    litero.resize(vnumber,vector<Minisat::Lit>(vnumber));
	

	//Creating nxk Matrix-----------------------------------------
	for (int i = 0;i<vnumber;i++)
	{
		for (int j=0;j<vcover;j++)
		{
			litero[i][j] = Minisat::mkLit(solver->newVar());	
		}
	}

	//clause 1----------------------------------------------------

	for (int i=0; i<vcover;i++)
	{
		for(int n=0;n<vnumber;n++)
		{	
			clause.push(litero[n][i]);
			//(x 1,i ∨ x 2,i ∨ · · · ∨ x n,i )
		}
		solver->addClause_(clause);
		clause.clear();
	}

	//clause 2-------------------------------------------------------

	for (int m=0; m<vnumber;m++)
	{
		for (int p=0;p<vcover;p++)
		{	
			for(int q=p+1;q<vcover;q++)
			{
				solver->addClause(~litero[m][p],~litero[m][q]);
				//(¬x m,p ∨ ¬x m,q )
			}
		}
	}

	//clause 3------------------------------------------------------------

	for (int m=0; m<vcover;m++)
	{
		for(int p=0;p<vnumber;p++)
		{
			for(int q=p+1;q<vnumber;q++)
			{
				solver->addClause(~litero[p][m],~litero[q][m]);             
				//(¬x p,m ∨ ¬x q,m )	
			}
		}
	}

	//clause 4--------------------------------------------------------------

	for (unsigned int i=0;i<eline.size()-2;i=i+2) //elength 4
	{
		Minisat::vec<Minisat::Lit> newclause;
		for (int k=0; k<vcover;k++)
		{
			newclause.push(litero[eline[i]][k]);
			newclause.push(litero[eline[i+1]][k]);
		}
		solver->addClause_(newclause);
		newclause.clear();
	}

	//Printing Vertex Cover---------------------------------------------------

	res = solver->solve();

    if(res==0)
    {
        min=vcover+1;
    }
    else
    {
        max=vcover-1;
        vc.clear();
        for (int i = 0;i<vnumber;i++)
        {
            for (int j=0;j<vcover;j++)
            {
                if(toInt(solver->modelValue(litero[i][j]))==0)
                {   
                vc.push_back(i);
                }
            }       
        }
    }		
}

if (calc_mode == true)
{
	int s = pthread_getcpuclockid(cnf_sat,&cid_sat);
	if (s!=0)
	{
		handle_error_en(s, "pthread_getcpuclockid");
	}
	time_sat = pclock(cid_sat);
	one = vc.size();
}

return NULL;
}

//////////////////////////////////////////////////////////////

void* APPROXER_1 (void* arg){

	vector <int> f=eline;
    newt.clear();

    f.erase(f.end()-2,f.end());
    vector<int>r=f;
    vector<int>foo;
    
while(true)
{
    foo = r;

    //sorting
    sort(r.begin(),r.end());

    pair<int, int> effVC = VC_picker(r.begin(), r.end());
    newt.push_back(effVC.first);
 
    r.clear();
    r=nutter(foo,newt[newt.size()-1]);
    foo.clear();    
   
    if(r.size()==0)
    {
        break;
    }
    else
    {
        continue;
    }   
}
sort (newt.begin(),newt.end());

if (calc_mode==true)
	{
		int s = pthread_getcpuclockid(approxer_1, &cid_app1);	                    
		if (s!=0)
		{
			handle_error_en(s, "pthread_getcpuclockid");
		}
		time_approx1 = pclock(cid_app1);
		two = newt.size();
	}

return NULL;
}

//////////////////////////////////////////////////////////////////

void* APPROXER_2 (void* arg){

    vector<int> f =eline;
    vertexCV.clear();

    f.erase(f.end()-2,f.end());
    vector<int>r=f;
    vector<int>foo;

while (true)
{    
    foo = r;
    //----------randomize
    srand (time(NULL));
    int ran_no;
    ran_no = 0 + (2*rand())% (foo.size());

    //-----------Picking edges
    vertexCV.push_back(foo[ran_no]);
    vertexCV.push_back(foo[ran_no+1]);

    r.clear();
    //cout<<"Edges to be removed from foo: "<<"<"<<vertexCV[vertexCV.size()-2]<<","<<vertexCV[vertexCV.size()-1]<<">"<<endl;
    r = nutter(foo,vertexCV[vertexCV.size()-2],vertexCV[vertexCV.size()-1]);
    foo.clear();
    if (r.size()==0)
    {
        break;
    }
    else
    {
        continue;
    }
}
sort(vertexCV.begin(),vertexCV.end());
if (calc_mode==true)
	{
		int s = pthread_getcpuclockid(approxer_2, &cid_app2);	                    	
		if (s!=0)
		{
			handle_error_en(s, "pthread_getcpuclockid");
		}
		time_approx2 = pclock(cid_app2);
		three = vertexCV.size();
	}

return NULL;
}

//////////////////////////////////////////////////////////

void printer()
{
cout<<"CNF-SAT-VC: ";
for (unsigned int i =0; i<vc.size();i++)
{
	if (i<vc.size()-1)
	{
    	cout<<vc[i]<<",";
	}
    else
    {
    	cout<<vc[i];
    }
}
cout<<endl;

if (calc_mode == true)
{
	cout<<time_sat<< " microseconds"<<endl;
}

cout<<"APPROX-VC-1: ";
for (unsigned int i=0;i<newt.size();i++)
{
    if (i<newt.size()-1)
    {
        cout<<newt[i]<<",";
    }
    else
    {
        cout<<newt[i];
    }
}

cout<<endl;
if (calc_mode == true)
{
	cout<<time_approx1<< " microseconds"<<endl;
}

cout<<"APPROX-VC-2: ";
for (unsigned int i = 0;i<vertexCV.size();i++)
{
    if (i<vertexCV.size()-1)
    {
        cout<<vertexCV[i]<<",";
    }
    else
    {
        cout<<vertexCV[i];
    }
}
cout<<endl;

if (calc_mode == true)
{
	cout<<time_approx2<< " microseconds"<<endl;
}

}


void run_timer()
{
	
	vector <long double> std_cnf,std_approx1,std_approx2;
	long double avg_cnf,avg_approx1,avg_approx2;
	long double sum_of_elems = 0.0;
	
	timer_cnf.push_back(time_sat);
	timer_approx1.push_back(time_approx1);
	timer_approx2.push_back(time_approx2);

	if (timer_cnf.size() == numb  && timer_approx1.size() == numb && timer_approx2.size() == numb)
	{
		for (std::vector<long double>::iterator it = timer_cnf.begin(); it!=timer_cnf.end();++it)
		{
			sum_of_elems += *it;	
		}
		avg_cnf=sum_of_elems/float(numb);
		cout<<"AVERAGE CNF: "<<  avg_cnf<<" microseconds"<<endl;	
		sum_of_elems = 0.0;
		for (std::vector<long double>::iterator it = timer_approx1.begin(); it!=timer_approx1.end();++it)
		{
			sum_of_elems += *it;	
		}
		avg_approx1=sum_of_elems/float(numb);
		cout<<"AVERAGE APPROXER 1: "<< avg_approx1<<" microseconds"<<endl;
		sum_of_elems = 0.0;
		for (std::vector<long double>::iterator it = timer_approx2.begin(); it!=timer_approx2.end();++it)
		{
			sum_of_elems += *it;	
		}
		avg_approx2 =sum_of_elems/float(numb);
		cout<<"AVERAGE APPROXER 2: "<<avg_approx2<<" microseconds"<<endl;
		sum_of_elems = 0.0;
	
		for (unsigned i =0;i<numb;i++)
		{	
		std_cnf.push_back(pow(timer_cnf[i]-avg_cnf,2));
		std_approx1.push_back(pow(timer_approx1[i]-avg_approx1,2));
		std_approx2.push_back(pow(timer_approx2[i]-avg_approx2,2));
		}

		if (std_approx1.size() == numb && std_approx2.size())
		{
			for (std::vector<long double>::iterator it = std_cnf.begin(); it!=std_cnf.end();++it)
			{
				sum_of_elems += *it;	
			}	
			long double s1 = sqrt(sum_of_elems/float(numb));
			cout<<"STD_SAT: "<<s1<<endl;
			sum_of_elems =0.0;
			for (std::vector<long double>::iterator it = std_approx1.begin(); it!=std_approx1.end();++it)
			{
				sum_of_elems += *it;	
			}
			long double s2 = sqrt(sum_of_elems/float(numb));
			cout<<"STD_APP1: "<<s2<<endl;
			sum_of_elems =0.0;
			for (std::vector<long double>::iterator it = std_approx2.begin(); it!=std_approx2.end();++it)
			{
				sum_of_elems += *it;	
			}
			long double s3 = sqrt(sum_of_elems/float(numb));
			cout<<"STD_APP2: "<<s3<<endl;
			sum_of_elems =0.0;

			timer_cnf.clear();
			std_cnf.clear();

			timer_approx1.clear();
			std_approx1.clear();

			timer_approx2.clear();
			std_approx2.clear();

		}
	}
	
	

}


void ap_ratio()
{	
	store1.push_back(float(two)/float(one));
	store2.push_back(float(three)/float(one));
	vector<float>store1_std,store2_std;
	float sum_of_elems=0.0,avg_ap1,avg_ap2;

	if (store2.size() == numb  && store1.size() == numb)
	{
		for (std::vector<float>::iterator it = store1.begin(); it!=store1.end();++it)
		{
			sum_of_elems += *it;	
		}
		avg_ap1=sum_of_elems/float(numb);
		cout<<"AVG APPROXIMATION RATIO (approx1/cnf) = "<<avg_ap1<<endl;
		sum_of_elems=0.0;

		for (std::vector<float>::iterator it = store2.begin(); it!=store2.end();++it)
		{
			sum_of_elems += *it;	
		}
		avg_ap2=sum_of_elems/float(numb);
		cout<<"AVG APPROXIMATION RATIO (approx2/cnf) = "<<avg_ap2<<endl;
		sum_of_elems=0.0;

		for (unsigned i =0;i<numb;i++)
		{	
		store1_std.push_back(pow(store1[i]-avg_ap1,2));
		store2_std.push_back(pow(store2[i]-avg_ap2,2));
		}
		
		if(store1_std.size()==numb && store2_std.size()==numb)
		{
			for (std::vector<float>::iterator it = store1_std.begin(); it!=store1_std.end();++it)
			{
				sum_of_elems += *it;	
			}	
			float s1 = sqrt(float(sum_of_elems)/float(numb));
			cout<<"STD_APP1 RATIO: "<<s1<<endl;
			sum_of_elems =0;
			for (std::vector<float>::iterator it = store2_std.begin(); it!=store2_std.end();++it)
			{
				sum_of_elems += *it;	
			}
			float s2 = sqrt(float(sum_of_elems)/float(numb));
			cout<<"STD_APP2 RATIO: "<<s2<<endl;
			sum_of_elems =0;

			store1.clear();
			store1_std.clear();

			store2.clear();
			store2_std.clear();
		}


	}
	else if ((store2.size() == ratio  && store1.size() == ratio) || store2.size()%ratio==0)
	{
		cout<<"CHANGE EDGES"<<endl;	
	}
}


void* I_O(void* arg)
{
	string comd;
    string cmd;
    
    string faltu1;
    string faltu2;
    char faltu3;

    bool decider;

	    while (!cin.eof())
	    {
	    	getline(cin,cmd);
	        stringstream conciser(cmd);

	        if (cin.eof())
	        {
	        	break;
	        }

	        conciser>>comd;
	        if(comd[0]=='V' || comd[0] =='v')
	        {
	            stringstream ssfaltu1(cmd);
	            ssfaltu1>>faltu1>>vcount;
	            if (vcount >=0)
	            {    
		            decider = true;
	            }
	        }
	        else if(comd[0]=='E' || comd[0] == 'e')
	        {
	            if (decider == true)
	            {
	                eline.clear();
	                stringstream ssfaltu3(cmd);
	                ssfaltu3>>faltu3>>faltu3;

	                if (faltu3 != '{')
	                {
	                    cerr<<"Error: Wrong Format."<<endl;
	                    continue;
	                }

	                char check1;
	                char check2;
	                char comma;
	                int no1,no2;

	                while(!ssfaltu3.eof())
	                {

	                    ssfaltu3>>check1>>no1>>comma>>no2>>check2>>faltu3;
	                    if (check1 == '}')
	                    {
	                        decider = false;
	                        eline.clear();
	                        continue;
	                    }
	                    else if (check1 != '<' || check2 != '>' || comma != ',')
	                    {
	                        cerr<<"Error: Incomplete edges."<<endl;
	                        decider = true;
	                        break;
	                    }
	                    else if (check1 == '<' && check2 == '>')
	                    {
	                        if (no1 >= vcount || no2 >= vcount)
	                        {
	                            cerr<<"Error: Pair <"<<no1<<","<<no2<<"> is out of range."<<endl;
	                            decider = true;
	                            break;
	                        }
	                        else
	                        {
	                            eline.push_back(no1);
	                            eline.push_back(no2);                     
	                        }
	                    }
	                    else
	                    {
	                        cerr<<"Error: Wrong Format."<<endl;
	                        break;
	                    }
	                    decider = false;
	                }
	       
	                if (decider == false && check1 != '}')
	                {
	                
	                    if (eline.size()>1 && decider == false && vcount >0)
	                    {	                    	
	                    	pthread_create(&cnf_sat,NULL,&CNF_SAT,NULL);
							pthread_create(&approxer_1,NULL,&APPROXER_1,NULL);
							pthread_create(&approxer_2,NULL,&APPROXER_2,NULL);
							
							pthread_join(cnf_sat,NULL);
							pthread_join(approxer_1,NULL);
							pthread_join(approxer_2,NULL);
				
	                	}
	                	printer();
	                	if (calc_mode == true)
	                	{
		                	ap_ratio();
		                	run_timer();
	                	}	                          
	                	eline.clear();
	                }
	            }
	            else
	            {
	                if ((faltu1 !="V"  || faltu1 != "v") && vcount >= 0)
	                {
	                    cerr<<"Error: Edges have been already entered."<<endl;    
	                }
	            
	            }
	        }
	    }



	    return NULL;
}

int main(int argc, char* argv[]){

if (argc == 2)
	{
		for (int i=1; i<argc;i++)
		{
			if (strcmp(argv[i],"-calc")==0)
			{
				//cout<<"CALCULATING AVERAGE AND STANDARD DEVIATION FOR "<<numb<<" RUNS"<<endl;
				calc_mode = true;
			}
		}
	}
pthread_t getliner;
pthread_create(&getliner,NULL,&I_O,NULL);
pthread_join(getliner,NULL);
    
   return 0;
}




