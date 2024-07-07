#include <ilcplex/ilocplex.h>
#include <time.h>
#include <vector>
#include <sstream>
#include <string>
ILOSTLBEGIN

//-------------Global Variables--------------
int i,j,n,k;
const int imax=10;//knapsacks in a set
const int jmax=70;//items in a set
const int nmax=1;
const int imaxstring=imax;
const int jmaxstring=jmax;
double U=0;//Total Capacity Allowed
double c[jmax];//profit of assignment of items
double d[imax];//cost of using knapsacks
double f[jmax];//weight/volume of items
double u[imax];//capacity of each knapsack
//const int m=100000;

//double epsilon=10;
double gap=0.05;//optimality gap for the Benders convergence criteria
double BBgap=0.1;//optimality gap for the Branch&Bound convergence criteria
double tolerance=0.01;
long double duration, duration_master;  // tracks time
int start=0,stop=0,start_master=0, stop_master=0 ;
int max_No_of_cuts=0;

double LowerBound=-1000000;
double LowerBoundGlobal=-1000000;

double MasterObj=0; // objective of master problem
double MasterObjFirst=0; // objective of the first master problem
double SlaveObjFunction=0; // objective function of slave problem
double OptimalMasterObjFunction=0; // optimal value of the objective function of master problem
double OptimalSlaveObjFunction=0; // optimal value of the objective function of slave problem
double OptimalOriginalObjFunction=0;// optimal value of theobjective function of the ORIGINAL PROBLEM

double BBOptimalMasterObjFunction=0; // optimal value of the objective function of master problem
double BBOptimalSlaveObjFunction=0; // optimal value of the objective function of slave problem
double BBOptimalOriginalObjFunction=0;// optimal value of theobjective function of the ORIGINAL PROBLEM

double XijValue[imax][jmax];
double YiValue[imax];
double YiValueFirst[imax];
double ThetaValue=0;
double ThetaValueFirst=0;

double OptimalXijValue[imax][jmax];
double OptimalYiValue[imax];
double OptimalThetaValue=0;

double BBOptimalXijValue[imax][jmax];
double BBOptimalYiValue[imax];
double BBOptimalThetaValue=0;

//--------Declare the environment of CPLEX----------------
IloEnv env;
//--------Construct models----------------
IloModel modelSlave1 (env);
IloModel modelMaster (env);	
//--------Construct Matrices----------------
typedef IloArray<IloNumArray> IloNumMatrix2x2;
typedef IloArray<IloNumMatrix2x2> IloNumMatrix3x3; 
typedef IloArray<IloNumMatrix3x3> IloNumMatrix4x4;

typedef IloArray<IloNumVarArray> IloNumVarMatrix2x2;
typedef IloArray<IloNumVarMatrix2x2> IloNumVarMatrix3x3;
typedef IloArray<IloNumVarMatrix3x3> IloNumVarMatrix4x4;

typedef IloArray<IloRangeArray> IloRangeMatrix2x2;
typedef IloArray<IloRangeMatrix2x2> IloRangeMatrix3x3;
typedef IloArray<IloRangeMatrix3x3> IloRangeMatrix4x4;

//------Declare Decision Variables----------
IloNumVarArray Yi(env,0);
IloNumVarArray Zn(env,0);
IloNumVarMatrix2x2 Xij(env,0);


//--------Declare Slave constraints-------------
IloRangeArray KnapCapi(env,0);
IloRangeMatrix2x2 VarXLessij(env,0);
IloRangeArray ItemOneKnapsackj(env,0);

//--------Declare dual variables of each constraint----------------

double S2valsDualRangeKnapCapi[imax];
double S2valsDualRangeVarXLessij[imax][jmax];
double S2valsDualRangeBranchCuts[jmax*imax];
double S2valsDualRangeItemOneKnapsackj[jmax];

//----------What does IloNum mean?---------------

IloNumArray valsDualRangeKnapCapi(env,0);
IloNum valsDualRangeVarXLessij;
IloNumArray valsDualRangeBranchCuts(env,0);
IloNumArray valsDualRangeItemOneKnapsackj(env,0);

IloNumArray FeasvalsDualRangeKnapCapi(env,0);

vector <int> IterationsNumber;
vector <int> BendersFEASCutsNumber;
vector <int> BendersOPTCutsNumber;
vector <double> BBLowerBoundArray;
vector <double> BBUpperBoundArray;
vector <double> Time;
double BBLowerBound=-1000000;
double BBUpperBound=1000000;

typedef struct treenode_tag {
	double  nodeUbound;  // LP bound
	IloModel  lp;     // ptr to master
	IloRangeArray  BranchCuts;   // ptr to slave
	int iBranching,jBranching,BranchingVar;//indices of Branching Variable
	double YiValueNode[imax],ThetaValueNode;
	treenode_tag  *nextnode;  // link to next node in tree

} treenode;

treenode_tag *BBTreeList;

void Found_Error(char *name)
{
	printf("%s failed, exiting...\n", name);
	printf("Press return to continue...\n");
    getchar();
}
int load_data(){
//-------------------Declare Data of the problem--------------------

for (j=0;j<jmax;j++){
	c[j]=0;
	f[j]=0;
}
for (i=0;i<imax;i++){
	d[i]=0;
	u[i]=0;
}
std::ostringstream os;
os << "C:\\Data_of_Knapsack_Problem\\Random\\KnapsackData(i" << imaxstring << ",j"<<jmaxstring<<").txt";
std::string FileName = os.str();
std::ifstream fsKnapsackData; 
fsKnapsackData.open(FileName.c_str(),std::ios::out);
for(j=0;j<jmax;j++){
	fsKnapsackData>>c[j];
}
for(i=0;i<imax;i++){
	fsKnapsackData>>d[i];
}
for(i=0;i<imax;i++){
	fsKnapsackData>>u[i];
}
fsKnapsackData>>U;
for(j=0;j<jmax;j++){
	fsKnapsackData>>f[j];
}
fsKnapsackData.close();

for (i=0;i<imax;i++){
	for (j=0;j<jmax;j++){
		XijValue[i][j]=0;
		OptimalXijValue[i][j]=0;
		BBOptimalXijValue[i][j]=0;
	}
	YiValue[i]=0;
	YiValueFirst[i]=0;
	OptimalYiValue[i]=0;
	BBOptimalYiValue[i]=0;

}

// Finish of DATA///////////////////////////
return 0;
}
int do_master(IloModel modelMaster_ptr){
//---------------------------------- MASTER ------------------------------------
//----------------------------- Master Variables --------------------------------
//------------------------ Decision Variable Yi ---------------------------------------

for (i=0;i<imax;i++){
	char KnapsackUse[70];  
	sprintf(KnapsackUse,"Yi(i%d)",i); 
    IloNumVar Y(env,0,1,ILOINT,KnapsackUse); 
    Yi.add(Y);
}

//--------------------------- Decision Variable Z ---------------------------

for (n=0;n<nmax;n++){
	char Theta[70];  
	sprintf(Theta,"Zn(n%d)",n); 
	IloNumVar Z(env,0,1000000,ILOFLOAT,Theta); 
	Zn.add(Z);
}
			
//-----------------------------Finish of Master Variables --------------------------------

//-------------------------Start of Master Constraints-----------------------------------------
//-------------------------- Total Capacity -------------------------

IloRangeArray TotalCapn(env,0);
for(n=0;n<nmax;n++){
	IloExpr expr(env,0);
	for(i=0;i<imax;i++){
		expr+=u[i]*Yi[i];
	}
	char TotalCapacity[60];
	sprintf(TotalCapacity,"TotalCapn(n%d)",n);
	double LBTotalCapn=0,UBTotalCapn=U;
	IloRange TotalCap(env,LBTotalCapn,expr,UBTotalCapn,TotalCapacity);
	modelMaster_ptr.add(TotalCap);
	TotalCapn.add(TotalCap);
	expr.end();
}

//---------------NO VALID INEQUALITIES-------------------
//-----------------------------------------------------------------------------
//-------------------------Finish of Master Constraints-----------------------------------------

//---------------------------Objective Function of master problem--------------------------
IloExpr expr1(env);

for (i=0;i<imax;i++){
	expr1-=d[i]*Yi[i];
}
for (n=0;n<nmax;n++){
	expr1+=Zn[n];
}

modelMaster_ptr.add(IloMaximize(env, expr1));
expr1.end();		

return 0;
}
int do_slave(IloModel modelSlave_ptr){

KnapCapi.clear();
VarXLessij.clear();
ItemOneKnapsackj.clear();

//--------------------------- PRIMAL SLAVE PROBLEM ----------------------------------
//------------------------------------------------------------------------------
//--------------------------- Slave Primal Variables ---------------------------
//---------------------------Decision Variable Xij ---------------------------

for (i=0;i<imax;i++){
	IloNumVarArray Xj(env,0);
	for (j=0;j<jmax;j++){	
		char ItemChoice[70];  
		sprintf(ItemChoice,"Xij(i%d,j%d)",i,j); 
        IloNumVar X(env,0,IloInfinity,ILOFLOAT,ItemChoice); 
        Xj.add(X);
	}
	Xij.add(Xj);
}

//-----------------  Finish of Decision Variables of PRIMAL SLAVE PROBLEM ------------------
//-----------------------------------------------------------------------------
//-------------------------Primal Slave Constraintes ------------------------
//-----------------------------------------------------------------------------
//--------------------------- Capacity of each Knapsack ------------------------------

for (i=0;i<imax;i++){
	IloExpr expr(env,0);
	for (j=0;j<jmax;j++){
		expr+=f[j]*Xij[i][j];
	}
	char KnapsackCapacity[60];
	sprintf(KnapsackCapacity,"KnapCapi(i%d)",i);
	double LBKnapCapi=-IloInfinity,UBKnapCapi=u[i]*YiValue[i];
	IloRange KnapCap(env,LBKnapCapi,expr,UBKnapCapi,KnapsackCapacity);
	modelSlave_ptr.add(KnapCap);
	KnapCapi.add(KnapCap);
	expr.end();
}


//--------------------------- Variable Xij<=1 ------------------------------

for (i=0;i<imax;i++){
	IloRangeArray VarXLessj(env,0);
	for (j=0;j<jmax;j++){
		IloExpr expr(env,0);
		expr=Xij[i][j];
		char VarXLessThanOne[60];
		sprintf(VarXLessThanOne,"VarXLessij(i%d,j%d)",i,j);
		double LBVarXLessij=-IloInfinity,UBVarXLessij=1;
		IloRange VarXLess(env,LBVarXLessij,expr,UBVarXLessij,VarXLessThanOne);
		modelSlave_ptr.add(VarXLess);
		VarXLessj.add(VarXLess);
		expr.end();
	}
	VarXLessij.add(VarXLessj);
}
//--------------------------- Sum(i) Xij<=1 ------------------------------

for (j=0;j<jmax;j++){
	IloExpr expr(env,0);
	for (i=0;i<imax;i++){
		expr+=Xij[i][j];
	}
	char EachItemToOneKnapsack[60];
	sprintf(EachItemToOneKnapsack,"ItemOneKnapsackj(j%d)",j);
	double LBItemOneKnapsackj=-IloInfinity,UBItemOneKnapsackj=1;
	IloRange ItemOneKnapsack(env,LBItemOneKnapsackj,expr,UBItemOneKnapsackj,EachItemToOneKnapsack);
	modelSlave_ptr.add(ItemOneKnapsack);
	ItemOneKnapsackj.add(ItemOneKnapsack);
	expr.end();
}


//------------------------------------------------------------------------------
//------------------------------------------------------------------------------
//------------------Objective Function of slave problem--------------------------
//------------------------------------------------------------------------------
IloExpr expr_slave(env);

for (i=0;i<imax;i++){
	for (j=0;j<jmax;j++){
		expr_slave+=c[j]*Xij[i][j];
	}
}

modelSlave_ptr.add(IloMaximize(env, expr_slave));
expr_slave.end();

return 0;
}



int BendersIteration(IloModel modelMaster_ptr, IloModel modelSlave_ptr, IloRangeArray BranchCuts_ptr,bool *InfeasibleMaster,int *loop,int *BDFeasCuts,int *BDOptCuts,treenode *parent_node,double NodeNumber){

int local_loop=0,local_BDFeasCuts=0,local_BDOptCuts=0,local_solve_master=0;
*InfeasibleMaster=false;
int branch_cuts_size=BranchCuts_ptr.getSize();

double DTransposeY=0,SlaveObjFunction=0;
LowerBound=-1000000;
LowerBoundGlobal=-1000000;
IloCplex cplexMaster_ptr(env);
IloCplex cplexSlave_ptr(env);
cplexMaster_ptr.setOut(env.getNullStream());
cplexSlave_ptr.setOut(env.getNullStream());
*loop=0;
*BDFeasCuts=0;
*BDOptCuts=0;

while ((MasterObj-LowerBoundGlobal)/MasterObj>gap && local_loop<10000){	
	local_loop++;
	
	//cout<<"-----------------"<<endl;
	//cout<<"Iteration ="<<local_loop<<endl;
	//cout<<"-----------------"<<endl;
	DTransposeY=0;
	
	if(local_loop>1 || NodeNumber==0){//if we are not in the first iteration or we are not in the first iteration of the first(ROOT) node(ParentBound=MasterObj=0)
		cplexMaster_ptr.extract(modelMaster_ptr);
		//--------------SOLVE MASTER PROBLEM----------------	
				
		try {
			
			cplexMaster_ptr.exportModel("MASTERAKI.lp");
			if(max_No_of_cuts<cplexMaster_ptr.getNrows()){
				max_No_of_cuts=cplexMaster_ptr.getNrows();
			}
			start_master = clock();
			cplexMaster_ptr.solve();
			stop_master = clock();
			duration_master += (long double) (stop_master-start_master)/CLOCKS_PER_SEC;
			local_solve_master++;
				
			if (!cplexMaster_ptr.solve ()){ 
				//env.error()<<"Failed to optimize Master."<<endl;
				//env.out()<<"----------------------------------------------------------------"<<endl;
				*InfeasibleMaster=true;
				break;
			}

			//env.out()<<"Solution status Master = "<<cplexMaster_ptr.getStatus()<<endl;
			//env.out()<<"Solution value Master= "<<cplexMaster_ptr.getObjValue()<<endl;

			//--------LOWER BOUND------------
			MasterObj=cplexMaster_ptr.getObjValue();

			for (i=0;i<imax;i++){
				YiValue[i]=cplexMaster_ptr.getValue(Yi[i]);
			}

			for (n=0;n<nmax;n++){
				ThetaValue=cplexMaster_ptr.getValue(Zn[n]);
			}

			for (i=0;i<imax;i++){
				DTransposeY-=d[i]*YiValue[i];
			}
			OptimalThetaValue=ThetaValue;

			if(local_loop==1 && NodeNumber==0){//if we solve the Master problem for the first iteration of the first node
				MasterObjFirst=MasterObj;
				for(i=0;i<imax;i++){
					YiValueFirst[i]=YiValue[i];
				}
				ThetaValueFirst=ThetaValue;
			}//endif we solve the Master problem for the first iteration of the first node

		}	
		catch ( IloException& e){
			cerr << "concert exception caught Master:"<<e<<endl;
		}
		catch (...){
			cerr<<"Unknown exception caught Master " <<endl;
		}

	}else{

		MasterObj=MasterObjFirst;
		for (i=0;i<imax;i++){
			YiValue[i]=YiValueFirst[i];
		}
		
		ThetaValue=ThetaValueFirst;
		OptimalThetaValue=ThetaValue;
		
		for (i=0;i<imax;i++){
			DTransposeY-=d[i]*YiValue[i];
		}

	}//end if we are not in the first iteration or we are not in the first iteration of the first(ROOT) node(ParentBound=MasterObj=0)

	if((MasterObj-LowerBoundGlobal)/MasterObj>gap){//if convergence is not achieved yet
	//---------------Update the LB of the constraints of SLAVE problem----------------
		for(i=0;i<imax;i++){
			KnapCapi[i].setUB(u[i]*YiValue[i]);	
		}
		
		cplexSlave_ptr.extract(modelSlave_ptr);
		//-----------Solve Slave Problem and add Benders Cut to Master--------------
		try {
			
			cplexSlave_ptr.setParam(IloCplex::PreInd,0); 
			cplexSlave_ptr.setParam(IloCplex::ScaInd,-1); 
			cplexSlave_ptr.setParam(IloCplex::RootAlg, IloCplex::Dual);//IMPORTANT
			cplexSlave_ptr.exportModel("modelSlave.lp");
			
			cplexSlave_ptr.solve();
			//env.out()<<"Solution status of SLAVE problem = " <<cplexSlave_ptr.getStatus()<<endl;
			//env.out()<<"Solution value of SLAVE problem = " <<cplexSlave_ptr.getObjValue()<<endl;

			if (!cplexSlave_ptr.solve ()){ //---------IF SLAVE1 IS INFEASIBLE-----
				//env.error()<<"Failed to optimize Slave LP."<<endl;
				//env.out()<<"----------------------------------------------------------------"<<endl;
				//------Lower Bound Global remains the same--------
				LowerBound=-1000000;
				LowerBoundGlobal=LowerBoundGlobal;
				//----------------Get an extreme ray of the DUAL SLAVE problem-------------
				//cout<<"size of Array ="<<FeasvalsDualRangeKnapCapi.getSize()<<endl;
				
				cplexSlave_ptr.dualFarkas(KnapCapi,FeasvalsDualRangeKnapCapi);
				//cout<<"size of Array ="<<FeasvalsDualRangeKnapCapi.getSize()<<endl;
				k=0;
				
				for (i=0;i<imax;i++){
					S2valsDualRangeKnapCapi[i]=-FeasvalsDualRangeKnapCapi[k];
					k++;
				}
				
				for (i=0;i<imax;i++){
						for (j=0;j<jmax;j++){
							S2valsDualRangeVarXLessij[i][j]=-FeasvalsDualRangeKnapCapi[k];
							k++;
						}
				}
				for (j=0;j<jmax;j++){
					S2valsDualRangeItemOneKnapsackj[j]=-FeasvalsDualRangeKnapCapi[k];
					k++;
				}

				if (branch_cuts_size>0){
					for (i=0;i<branch_cuts_size;i++){
						S2valsDualRangeBranchCuts[i]=-FeasvalsDualRangeKnapCapi[k];
						k++;
					}
				}
				//cout<<"k ="<<k<<endl;


				//---------CREATION OF BENDERS FEASIBILITY CUT--------------- 

				IloExpr expr101(env);

				for (i=0;i<imax;i++){
					expr101+=S2valsDualRangeKnapCapi[i]*(u[i]*Yi[i]);
				}

				for (i=0;i<imax;i++){
					for (j=0;j<jmax;j++){
						expr101+=S2valsDualRangeVarXLessij[i][j];
					}
				}
				for (j=0;j<jmax;j++){
					expr101+=S2valsDualRangeItemOneKnapsackj[j];
				}
				if (branch_cuts_size>0){
					for (i=0;i<branch_cuts_size;i++){
						expr101+=S2valsDualRangeBranchCuts[i]*BranchCuts_ptr[i].getUB();
					}
				}

				//--------------ADD BENDERS FEASIBILITY CUT TO MASTER----------------
				char MasterFeasibilityCut[90];
				sprintf(MasterFeasibilityCut,"FeasibilityCut(iter%d)",local_loop);
				double LB101=0,UB101=IloInfinity;
				IloRange CTMaster(env,LB101,expr101,UB101,MasterFeasibilityCut);
				modelMaster_ptr.add(CTMaster);
				expr101.end();
				local_BDFeasCuts++;
							
			}//Finish of IF SLAVE PROBLEM IS INFEASIBLE
				
			else { //------------- IF SLAVE PROBLEM IS FEASIBLE------------
				
				//env.out()<<"Found a FEASIBLE solution of Slave LP"<<endl;
				//env.out()<<"----------------------------------------------------------------"<<endl;
				SlaveObjFunction=cplexSlave_ptr.getObjValue();
				for (i=0;i<imax;i++){
					for (j=0;j<jmax;j++){
						XijValue[i][j]=cplexSlave_ptr.getValue(Xij[i][j]);	
					}
				}
				LowerBound= DTransposeY + SlaveObjFunction;
							
				if( LowerBound <= LowerBoundGlobal){//-----We found a worse feasible solution---
					LowerBoundGlobal=LowerBoundGlobal;
				}else{//-----------We found a better feasible solution-------
					LowerBoundGlobal= LowerBound;//Update Lower Bound
					OptimalOriginalObjFunction=LowerBoundGlobal;
					OptimalMasterObjFunction=DTransposeY;
					OptimalSlaveObjFunction=SlaveObjFunction;
					for (i=0;i<imax;i++){
						OptimalYiValue[i]=YiValue[i];
						for (j=0;j<jmax;j++){
							OptimalXijValue[i][j]=XijValue[i][j];	
						}
					}
					OptimalThetaValue=ThetaValue;
					
				}//end of else (better feasible solution found)

				

				if((MasterObj-LowerBoundGlobal)/MasterObj>gap){//if convergence is not achieved yet

					//---------------------Get an extreme point of DUAL SLAVE problem--------------------

					//cout<<"size of Array ="<<valsDualRangeKnapCapi.getSize()<<endl;
				
					cplexSlave_ptr.getDuals(valsDualRangeKnapCapi,KnapCapi);
					//cout<<"size of Array ="<<valsDualRangeKnapCapi.getSize()<<endl;
					
					for (i=0;i<imax;i++){
						S2valsDualRangeKnapCapi[i]=valsDualRangeKnapCapi[i];
					}
					
					for (i=0;i<imax;i++){
						for (j=0;j<jmax;j++){
							valsDualRangeVarXLessij=cplexSlave_ptr.getDual(VarXLessij[i][j]);
							S2valsDualRangeVarXLessij[i][j]=valsDualRangeVarXLessij;
								
						}
					}
					//cout<<"size of Array ="<<valsDualRangeItemOneKnapsackj.getSize()<<endl;
					cplexSlave_ptr.getDuals(valsDualRangeItemOneKnapsackj,ItemOneKnapsackj);
					//cout<<"size of Array ="<<valsDualRangeItemOneKnapsackj.getSize()<<endl;
					for (j=0;j<jmax;j++){
						S2valsDualRangeItemOneKnapsackj[j]=valsDualRangeItemOneKnapsackj[j];
					}
					//cout<<"size of Array ="<<valsDualRangeBranchCuts.getSize()<<endl;
					if (branch_cuts_size>0){
						cplexSlave_ptr.getDuals(valsDualRangeBranchCuts,BranchCuts_ptr);
						//cout<<"size of Array ="<<valsDualRangeBranchCuts.getSize()<<endl;
						for (i=0;i<branch_cuts_size;i++){
							S2valsDualRangeBranchCuts[i]=valsDualRangeBranchCuts[i];
						}
					}

					//---------CREATION OF BENDERS OPTIMALITY CUT--------------- 

					IloExpr exprOptimality(env);

					for (i=0;i<imax;i++){
						exprOptimality+=S2valsDualRangeKnapCapi[i]*(u[i]*Yi[i]);
					}

					for (i=0;i<imax;i++){
						for (j=0;j<jmax;j++){
							exprOptimality+=S2valsDualRangeVarXLessij[i][j];
						}
					}
					for (j=0;j<jmax;j++){
						exprOptimality+=S2valsDualRangeItemOneKnapsackj[j];
					}
					if (branch_cuts_size>0){
						for (i=0;i<branch_cuts_size;i++){
							exprOptimality+=S2valsDualRangeBranchCuts[i]*BranchCuts_ptr[i].getUB();
						}
					}
					for (n=0;n<1;n++){
						exprOptimality-=Zn[n];
					}

					//--------------ADD BENDERS OPTIMALITY CUT TO MASTER----------------

					char MasterOptimalityCut[90];
					sprintf(MasterOptimalityCut,"OptimalityCut(iter%d)",local_loop);
					double LB101=0,UB101=IloInfinity;
					IloRange CTMaster(env,LB101,exprOptimality,UB101,MasterOptimalityCut);
					modelMaster_ptr.add(CTMaster);
					exprOptimality.end();
					local_BDOptCuts++;
				}//endif convergence is not achieved yet

			}//end of else (FEASIBLE SLAVE PROBLEM)


		}//end of first try(try of primal slave 1)
		
		catch ( IloException& e){
			cerr << "concert exception caught:"<<e<<endl;
		}
		catch (...){
			cerr<<"Unknown exception caught" <<endl;
		}

	}//endif convergence is not achieved yet

	//------------ Before we got to loop t+1 and solve the new Master Problem we update the LB and UB---- 

/*	
	for (i=0;i<imax;i++){
		if(YiValue[i]!=0){
			cout<<"YiValue"<<"["<<i<<"]="<<YiValue[i]<<endl;
		}
			
	}
	cout<<"----------------------------------"<<endl;

	
	for (i=0;i<imax;i++){
		for (j=0;j<jmax;j++){
			if(XijValue[i][j]!=0){
				cout<<"XijValue"<<"["<<i<<"]"<<"["<<j<<"]="<<XijValue[i][j]<<endl;
			}
		}
	}
	cout<<"----------------------------------"<<endl;

	
	if(ThetaValue!=0){
		cout<<"ThetaValue="<<ThetaValue<<endl;
	}
	if(DTransposeY!=0){
		cout<<"DTransposeY="<<DTransposeY<<endl;
	}
	if(SlaveObjFunction!=0){
		cout<<"SlaveObjFunction="<<SlaveObjFunction<<endl;
	}
	
	cout<<"LowerBound="<<LowerBoundGlobal<<endl;

	cout<<"UpperBound="<<MasterObj<<endl;

	std::ofstream fsLowerBound; 
	fsLowerBound.open("C:\\Code_Results\\LowerBound.txt",std::ios::app );
	fsLowerBound<<LowerBound<< std::endl;
	fsLowerBound.close();

	std::ofstream fsUpperBound; 
	fsUpperBound.open("C:\\Code_Results\\UpperBound.txt",std::ios::app );
	fsUpperBound<<MasterObj<< std::endl;
	fsUpperBound.close();

	std::ofstream fsLowerBoundGlobalArray; 
	fsLowerBoundGlobalArray.open("C:\\Code_Results\\LowerBoundGlobalArray.txt",std::ios::app );
	fsLowerBoundGlobalArray<<LowerBoundGlobal<< std::endl;
	fsLowerBoundGlobalArray.close();

	std::ofstream fsThetaValue; 
	fsThetaValue.open("C:\\Code_Results\\ThetaValue.txt",std::ios::app );
	fsThetaValue<<ThetaValue<< std::endl;
	fsThetaValue.close();

	
	cout<<"-----------------"<<endl;
	cout<<"------fIN--------"<<endl;
*/
}//end of loop

*loop=local_solve_master;
*BDFeasCuts=local_BDFeasCuts;
*BDOptCuts=local_BDOptCuts;
cplexMaster_ptr.end();
cplexSlave_ptr.end();

return 0;
}//end of BendersIteration

int FindBranchingVariable(int *BranchingVar, int *iBranching, int *jBranching){
*iBranching=0;
*jBranching=0;
*BranchingVar=-1;
for(i=0;i<imax;i++){
	for(j=0;j<jmax;j++){
		if(OptimalXijValue[i][j]>tolerance && OptimalXijValue[i][j]<1-tolerance){//find the first fractional variable
			*iBranching=i;
			*jBranching=j;
			*BranchingVar=1;
			break;
		}
	}
	if(*BranchingVar==1)break;
}
//cout<<"iBranching="<<*iBranching<<endl;
//cout<<"jBranching="<<*jBranching<<endl;
//cout<<"BranchingVar="<<*BranchingVar<<endl;

return 0;
}//end of FindBranchingVariable



int PrintOptimalSolution(){
	std::ostringstream os;
	os << "C:\\Code_Results\\ExtraConstraintRandom\\KnapsackResults(i" << imaxstring << ",j"<<jmaxstring<<")\\WithOUT LOCAL CUTS - OptimalSolution(i" << imaxstring << ",j"<<jmaxstring<<").txt";
	std::string FileName = os.str();
	
	std::ofstream fsOptimalSolution; 
	fsOptimalSolution.open(FileName.c_str(),std::ios::app );
	fsOptimalSolution<<"TotalSolutionTime= "<<duration<<" seconds "<< std::endl;
	if((BBUpperBound-BBLowerBound)/BBUpperBound>0){
		fsOptimalSolution<<"OptimalityGap= "<<(BBUpperBound-BBLowerBound)/BBUpperBound<< std::endl;
	}else{
		fsOptimalSolution<<"OptimalityGap= 0"<< std::endl;
	}
	fsOptimalSolution<<"OptimalObjFunction="<<BBOptimalOriginalObjFunction<< std::endl;
	fsOptimalSolution<<"OptimalMasterObjFunction="<<BBOptimalMasterObjFunction<< std::endl;
	fsOptimalSolution<<"OptimalSlaveObjFunction="<<BBOptimalSlaveObjFunction<< std::endl;
	fsOptimalSolution<<"----------------------------------"<< std::endl;
	if(BBOptimalThetaValue>0.01){
		fsOptimalSolution<<"OptimalThetaValue="<<BBOptimalThetaValue<<std::endl;
	}	
	fsOptimalSolution<<"----------------------------------"<< std::endl;
	for (i=0;i<imax;i++){
		if(BBOptimalYiValue[i]>0.01){
			fsOptimalSolution<<"OptimalYiValue"<<"["<<i<<"]="<<BBOptimalYiValue[i]<<std::endl;
		}	
	}
	fsOptimalSolution<<"----------------------------------"<< std::endl;
	for (i=0;i<imax;i++){
		for (j=0;j<jmax;j++){
			if(BBOptimalXijValue[i][j]>0.01){
				fsOptimalSolution<<"OptimalXijValue"<<"["<<i<<"]"<<"["<<j<<"]="<<BBOptimalXijValue[i][j]<<std::endl;
			}
		}
	}
	fsOptimalSolution.close();

	std::ostringstream Iterations;
	Iterations << "C:\\Code_Results\\ExtraConstraintRandom\\KnapsackResults(i" << imaxstring << ",j"<<jmaxstring<<")\\WithOUT LOCAL CUTS - IterationsNumber(i" << imaxstring << ",j"<<jmaxstring<<").txt";
	std::string FileNameIterations = Iterations.str();
	std::ofstream fsIterationsNumber; 
	fsIterationsNumber.open(FileNameIterations.c_str(),std::ios::app );
	for (i=0;i<IterationsNumber.size();i++){
		fsIterationsNumber<<IterationsNumber.at(i)<< std::endl;
	}
	fsIterationsNumber.close();


	std::ostringstream FeasibilityCuts;
	FeasibilityCuts << "C:\\Code_Results\\ExtraConstraintRandom\\KnapsackResults(i" << imaxstring << ",j"<<jmaxstring<<")\\WithOUT LOCAL CUTS - BendersFEASCutsNumber(i" << imaxstring << ",j"<<jmaxstring<<").txt";
	std::string FileNameFeasibilityCuts = FeasibilityCuts.str();
	std::ofstream fsFeasibilityCuts; 
	fsFeasibilityCuts.open(FileNameFeasibilityCuts.c_str(),std::ios::app );
	for (i=0;i<BendersFEASCutsNumber.size();i++){
		fsFeasibilityCuts<<BendersFEASCutsNumber.at(i)<< std::endl;
	}
	fsFeasibilityCuts.close();

	std::ostringstream OptimalityCuts;
	OptimalityCuts << "C:\\Code_Results\\ExtraConstraintRandom\\KnapsackResults(i" << imaxstring << ",j"<<jmaxstring<<")\\WithOUT LOCAL CUTS - BendersOPTCutsNumber(i" << imaxstring << ",j"<<jmaxstring<<").txt";
	std::string FileNameOptimalityCuts = OptimalityCuts.str();
	std::ofstream fsOptimalityCuts; 
	fsOptimalityCuts.open(FileNameOptimalityCuts.c_str(),std::ios::app );
	for (i=0;i<BendersOPTCutsNumber.size();i++){
		fsOptimalityCuts<<BendersOPTCutsNumber.at(i)<< std::endl;
	}
	fsOptimalityCuts.close();


	std::ostringstream LowerBound;
	LowerBound << "C:\\Code_Results\\ExtraConstraintRandom\\KnapsackResults(i" << imaxstring << ",j"<<jmaxstring<<")\\WithOUT LOCAL CUTS - BBLowerBound(i" << imaxstring << ",j"<<jmaxstring<<").txt";
	std::string FileNameLB = LowerBound.str();
	std::ofstream fsBBLowerBound; 
	fsBBLowerBound.open(FileNameLB.c_str(),std::ios::app );
	for (i=0;i<BBLowerBoundArray.size();i++){
		fsBBLowerBound<<BBLowerBoundArray.at(i)<< std::endl;
	}
	fsBBLowerBound.close();

	std::ostringstream UpperBound;
	UpperBound << "C:\\Code_Results\\ExtraConstraintRandom\\KnapsackResults(i" << imaxstring << ",j"<<jmaxstring<<")\\WithOUT LOCAL CUTS - BBUpperBound(i" << imaxstring << ",j"<<jmaxstring<<").txt";
	std::string FileNameUB = UpperBound.str();
	std::ofstream fsBBUpperBound; 
	fsBBUpperBound.open(FileNameUB.c_str(),std::ios::app );
	for (i=0;i<BBUpperBoundArray.size();i++){
		fsBBUpperBound<<BBUpperBoundArray.at(i)<< std::endl;
	}
	fsBBUpperBound.close();

	std::ostringstream TimePath;
	TimePath << "C:\\Code_Results\\ExtraConstraintRandom\\KnapsackResults(i" << imaxstring << ",j"<<jmaxstring<<")\\WithOUT LOCAL CUTS - Time(i" << imaxstring << ",j"<<jmaxstring<<").txt";
	std::string FileNameTime = TimePath.str();
	std::ofstream fsBBTime; 
	fsBBTime.open(FileNameTime.c_str(),std::ios::app );
	for (i=0;i<Time.size();i++){
		fsBBTime<<Time.at(i)<< std::endl;
	}
	fsBBTime.close();

return 0;
}


void AddNewNodeToList(IloModel modelMaster_ptr, IloRangeArray BranchCuts_ptr, const double upper_bound, int iBranch_ptr, int jBranch_ptr, int BranchVar_ptr)
{
	treenode_tag *Node,*K,*P;
	Node = (treenode_tag *)malloc(sizeof(treenode_tag));
	Node->lp = modelMaster_ptr;
	Node->BranchCuts = BranchCuts_ptr;
	Node->nodeUbound = upper_bound;
	Node->iBranching = iBranch_ptr;
	Node->jBranching = jBranch_ptr;
	Node->BranchingVar = BranchVar_ptr;
	for(i=0;i<imax;i++){
		Node->YiValueNode[i]=OptimalYiValue[i];
	}
	Node->ThetaValueNode=OptimalThetaValue;
	Node->nextnode=NULL;
	//printf("The nodeUbound is= %Lf \n", Node->nodeUbound);

	if (BBTreeList == NULL || BBTreeList->nodeUbound <= Node->nodeUbound){ // if list is empty or the new node has the highest bound
			Node->nextnode = BBTreeList;
		    BBTreeList = Node; // add to front
	}else{
		K = BBTreeList;
		P = K->nextnode;
		while(P != NULL && P->nodeUbound > Node->nodeUbound){
			K = P;
			P = P->nextnode;
		}
		K->nextnode = Node;
		Node->nextnode = P;
	}
}


int CreateChild(treenode *parent_node, int rhs_value,int NodeNumber)
{
	int status,BranchingVar=0,ii=0,jj=0,loop=0,BDFeasCuts=0,BDOptCuts=0;
	bool InfeasibleMaster; 
	int iBranching_parent=parent_node->iBranching;
	int jBranching_parent=parent_node->jBranching;

	
	IloModel child_master(env);
	IloModel child_slave(env);
	IloRangeArray child_BranchCuts(env,0);

	//child_master.add(parent_node->lp);//copy the last Master Problem of its parent
	status=do_master(child_master);
	if (status != 0){
		Found_Error("do_slave");
		return -1;
	}	
	
	IloCplex cplexMaster_ptr(env);
	cplexMaster_ptr.extract(child_master);

	status=do_slave(child_slave);
	if (status != 0){
		Found_Error("do_slave");
		return -1;
	}
	
	child_BranchCuts.add(parent_node->BranchCuts);

	if(rhs_value==0){//we create the left child (add the cut BranchingVariable<=0)
		IloExpr exprLeft(env);
		exprLeft=Xij[iBranching_parent][jBranching_parent];
		char LeftCut[90];
		sprintf(LeftCut,"LeftCut");
		double LBLeft=-IloInfinity,UBLeft=0;
		IloRange LeftSlaveCut(env,LBLeft,exprLeft,UBLeft,LeftCut);
		child_BranchCuts.add(LeftSlaveCut);
		exprLeft.end();
	}else{//we create the right child (add the cut BranchingVariable>=1)
		IloExpr exprRight(env);
		exprRight=-Xij[iBranching_parent][jBranching_parent];
		char RightCut[90];
		sprintf(RightCut,"RightCut");
		double LBRight=-IloInfinity,UBRight=-1;
		IloRange RightSlaveCut(env,LBRight,exprRight,UBRight,RightCut);
		child_BranchCuts.add(RightSlaveCut);
		exprRight.end();
	}
	child_slave.add(child_BranchCuts);

	status = BendersIteration(child_master, child_slave, child_BranchCuts,&InfeasibleMaster,&loop, &BDFeasCuts,&BDOptCuts,parent_node,NodeNumber);// generate columns in order to solve new master
	if (status != 0 ){
		Found_Error("BendersIteration");
		return -1; 
	}
	IterationsNumber.push_back(loop);
	BendersFEASCutsNumber.push_back(BDFeasCuts);
	BendersOPTCutsNumber.push_back(BDOptCuts);
	if(InfeasibleMaster==false){
		status = FindBranchingVariable(&BranchingVar,&ii,&jj);
		if (status != 0 ){
		   Found_Error("FindBranchingVariable");
		   return -1;
		}
		if(BranchingVar==1)AddNewNodeToList(child_master,child_BranchCuts,MasterObj,ii,jj,BranchingVar); 
		
		if(BranchingVar==-1 && BBLowerBound<LowerBoundGlobal){//if an integer solution is achieved and it is the best so far
				BBLowerBound= LowerBoundGlobal;//Update Lower Bound
				BBOptimalOriginalObjFunction=BBLowerBound;
				BBOptimalMasterObjFunction=OptimalMasterObjFunction;
				BBOptimalSlaveObjFunction=OptimalSlaveObjFunction;
				for (i=0;i<imax;i++){
					BBOptimalYiValue[i]=OptimalYiValue[i];
					for (j=0;j<jmax;j++){
						BBOptimalXijValue[i][j]=OptimalXijValue[i][j];	
					}
				}
				BBOptimalThetaValue=OptimalThetaValue;
		}//end if an integer solution is achieved and it is the best so far
	}//end if InfeasibleMaster==false
	
	child_slave.end();
	cplexMaster_ptr.end();
	return 0;
}




void DeleteFromList(IloEnv env, treenode_tag *lpnode_ptr,int BranchNumber)
{
	treenode_tag *Node, *K;
	Node = BBTreeList;
	K = BBTreeList->nextnode;
	if (BBTreeList == lpnode_ptr){
		BBTreeList = BBTreeList->nextnode;
		//Node->lp.end();
		Node->BranchCuts.end();
		free(Node);
	}else{
		while (K !=NULL){
			if (K == lpnode_ptr){
				Node->nextnode = K->nextnode;
				//K->lp.end();
				K->BranchCuts.end();
				K=NULL;
				free(K);
				break;
			} else {
				Node = K;
				K = K->nextnode;
			}
		}//end of while
	}//end of else
}

int Branch()
{
	bool InfeasibleMaster;
	int loop=0,BDFeasCuts=0,BDOptCuts=0,rhs_value, status,ii,jj;
	int BranchingVar,BranchNumber=0,NodeNumber=0; // contains the index of the var upon which branching is performed;
	IloRangeArray BranchCutsFirstNode(env,0);
	IterationsNumber.clear();
	BendersFEASCutsNumber.clear();
	BendersOPTCutsNumber.clear();
	BBLowerBoundArray.clear();
	BBUpperBoundArray.clear();
	Time.clear();
	treenode_tag *parent_node;
    
	BBTreeList = (treenode_tag *)malloc(sizeof(treenode_tag)); 
    BBTreeList=NULL;

	status=BendersIteration(modelMaster, modelSlave1, BranchCutsFirstNode,&InfeasibleMaster,&loop,&BDFeasCuts,&BDOptCuts,BBTreeList,NodeNumber);
	if (status != 0){
		Found_Error("BendersIteration");
		return -1;
	}
	
	IterationsNumber.push_back(loop);
	BendersFEASCutsNumber.push_back(BDFeasCuts);
	BendersOPTCutsNumber.push_back(BDOptCuts);
    
	status = FindBranchingVariable(&BranchingVar,&ii,&jj);
	if (status != 0 ){
	   Found_Error("FindBranchingVariable");
	   return -1;
	}

	AddNewNodeToList(modelMaster, BranchCutsFirstNode, MasterObj,ii,jj,BranchingVar);//add the first node to the list
    parent_node = BBTreeList;
	BBUpperBound=parent_node->nodeUbound;  

	while ((BBUpperBound-BBLowerBound)/BBUpperBound>BBgap){  //while convergence is not achieved yet
		BranchNumber++;
		//printf("BranchNumber=%d\n",BranchNumber);

		for (rhs_value=0; rhs_value<=1; rhs_value++) // one for left branch (rhs = 0) and one for right branch (rhs = 1)
		{
			NodeNumber++;
			status = CreateChild(parent_node, rhs_value,NodeNumber); // adds the child node to the branch and bound tree
			if (status != 0 ){
				Found_Error("CreateChild");
				return -1;
			}
		}   
		if (BBTreeList->nextnode != NULL){ 
			DeleteFromList(env, parent_node,BranchNumber); // if additional nodes exist in tree, delete the node that was just explored
		}else{ 
			break;
		}

		parent_node = BBTreeList;  // select the most promising node (the first one that has the lowest LP bound) in the tree
		//cout<<"BranchingVar="<<parent_node->BranchingVar<<endl;
		BBUpperBound=parent_node->nodeUbound;//Update the Global Upper Bound of B&B procedure
		BBLowerBoundArray.push_back(BBLowerBound);
		if(BBUpperBound>=BBLowerBound){
			BBUpperBoundArray.push_back(BBUpperBound);
		}else{
			BBUpperBoundArray.push_back(BBLowerBound);
		}
		Time.push_back((long double)(clock()-start)/CLOCKS_PER_SEC);
		cout<<"BBUpperBound = "<<BBUpperBound<<endl;
		cout<<"BBLowerBound = "<<BBLowerBound<<endl;
    }// end while
	
    return 0;
}

int main (int argc, char **argv)
{
int  status;

start = clock();

status=load_data();
if (status != 0){
	Found_Error("load_data");
	return -1;
}

status=do_master(modelMaster);
if (status != 0){
	Found_Error("do_master");
	return -1;
}

status=do_slave(modelSlave1);
if (status != 0){
	Found_Error("do_slave");
	return -1;
}

status=Branch();
if (status != 0){
	Found_Error("Branch");
	return -1;
}

stop = clock();
duration = (long double) (stop-start)/CLOCKS_PER_SEC;

status=PrintOptimalSolution();
if (status != 0){
	Found_Error("PrintOptimalSolution");
	return -1;
}

env.end();

printf("BBLowerBound = %Lf \n", BBLowerBound);
if((BBUpperBound-BBLowerBound)/BBUpperBound>0){
	printf("Optimality Gap = %Lf \n",(BBUpperBound-BBLowerBound)/BBUpperBound);
}else{
	printf("Optimality Gap = 0 \n");
}
printf("Code terminated successfully \n");
printf("Execution time = %Lf seconds\n", duration);
printf("Percentage of master time = %f percent\n", duration_master*100/duration);
printf("Maximum No of cuts in Master Problem = %d \n", max_No_of_cuts-1);

return 0;

} //End main




