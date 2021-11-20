/*********************************************
 * OPL 12.8.0.0 Model
 * Author: kamnis
 * Creation Date: Apr 11, 2019 at 9:59:09 AM
 *********************************************/
 
// params

int f = ...;  	// number of functions
int s = ...;  	// number of signals
int c = ...;  	// number of nodes
int b = ...;  	// number of buses
int p = ...;    // number of paths

int BIG_M = ...;
float EPS = ...;

float CONTEXT_SWITCH_COST = ...;



range F = 1..f; /**  array or range of functions **/
range S = 1..s; /**  array or range of functions **/
range C = 1..c; /**  array or range of nodes     **/
range B = 1..b; /**  array or range of nodes     **/
range P = 1..p; /**  array or range of paths     **/



// data Sets

  
// pair of functions <f1,f2>
// pair of functions <s1,s2>
// pair tuple used as primary key

tuple pair{
	int i;
	int j;
}


// triple tuple as id

tuple triple{
	int i;
	int j;
	int k;

}

    
tuple node {
		int id;
		float capacity; // node utilization capacity e.g. 0.8

}

	//NB the set of execution nodes communication through the bus
tuple bus {
		int id;
		float capacity;
		{int} NB;		
}

tuple function {
	int id;
	int period;
}

tuple signal {
	int id;
	int period;
	int sen;
	{int} rec;
}

tuple path{
	int id;
	int source;
	int sink;
	int deadline;
} 


/**
  *  placementPossibility is a set of 
  *	 pairs that gathers all possible placements
  **/
  
{pair} FunctionPlacementPossibilitySet = {<i,j> | i in F, j in C };

{pair} SignalplacementPossibilitySet = {<i,j> | i in S, j in B };

{triple} placementInSameNodePossibilitySet = {<i,j,k> | i,j in F, k in C : i!=j};

{triple} placementInSameBusPossibilitySet = {<i,j,k> | i,j in S, k in B : i!=j};

{pair} setOfPairsOfFunctions = {<i,j> | i,j in F : i!=j};

{pair} setOfPairsOfSignals = {<i,j> | i,j in S : i!=j};



// to use as index within the SnHp binary variable
{triple} placementPrioritySet = { <i,j,k> | i,j in F, k in C : i != j};


{triple} SignalsPlacementPrioritySet = { <i,j,k> | i,j in S, k in B : i != j };



{function} 	functionSet		= ... ; 

{signal} 	signalSet		= ... ; 

{path} pathSet = ...;

{node} nodeSet 	= ...;

{bus} busSet  	= ...;


int wcetOfFunctionOnNodeSet[FunctionPlacementPossibilitySet]  = ...;
int wcetOfSignalOnBusSet[SignalplacementPossibilitySet]  = ...;


// dp and Xi are two params to indicate directly if  


// in case of dp : the execution of fi denpends on fj
int dp[setOfPairsOfFunctions] = ...;

// in case of Xi : the fi and fj are concurrent (i.e they don't belong to the same path)
int Xi[setOfPairsOfFunctions] = ...;

// in case of Xis : the Si and Sj are concurrent (i.e they don't belong to the same path)
int Xis[setOfPairsOfSignals] = ...;



// decision vars


dvar boolean A[FunctionPlacementPossibilitySet];
dvar boolean X[placementInSameNodePossibilitySet];


dvar boolean AS[SignalplacementPossibilitySet];
dvar boolean G[S];
dvar boolean XS[placementInSameBusPossibilitySet];


dvar boolean Psi[setOfPairsOfFunctions];
dvar boolean SPsi[setOfPairsOfSignals];

dvar boolean SnHp[placementPrioritySet];
dvar boolean SnDp[placementPrioritySet];
dvar boolean SnSp[placementPrioritySet];



dvar boolean SnHpS[SignalsPlacementPrioritySet];

dvar boolean SnSpS[SignalsPlacementPrioritySet];


dvar float+ J[F];
dvar float+ R[F];
dvar float+ W[F];

dvar int+ Sigma[setOfPairsOfFunctions];

// I have changed the type of the I variable from Boolean to int

dvar int+ I[placementPrioritySet];

dvar int Phi[F];
dvar int Theta[setOfPairsOfFunctions];


// dvars for signals WCRT computation

dvar float+ JS[S];
dvar float+ RS[S];
dvar float+ WS[S];

dvar int SigmaS[setOfPairsOfSignals];

// I have changed the type of the IS variable from Boolean to int

dvar int+ IS[SignalsPlacementPrioritySet];
dvar int BS[S];


	// *** additional vars for jitter formulation according to the nature of the communication ***

	// inter-task communication
dvar float+ Alpha[S];

	// intra-task communication
dvar float+ Zeta[S];

	// jitter of remote signals
	
dvar float+ Lamda[SignalsPlacementPrioritySet];

	// PATH latency

dvar float+ L[P];



// Equation 64


// model (objective function)

minimize sum(i in pathSet)( L[i.id])/card(pathSet);

/**
 * sub-section 1 functions placement
 **/
 
 
 // Formula 14
 
 // It is about allocating the function i in one and only one node k
 // A is an array of binary decision variable. It stands for Allocation

subject to {

	forall(i in functionSet){
		sum(k in nodeSet) A[<i.id,k.id>] == 1;
	}		
}




//Equation 16


// Allows the definition X based on A
// X[1,2,1] = 1 implies function 1 and function 2 are placed on the same node 1
// if they are already placed on a given node, then X = 0 for all other nodes



subject to {

	forall(i,j in functionSet : i.id != j.id ){
		forall(k in nodeSet){	
			fi_and_fj_are_placed_on_the_same_node_or_not :
			A[<i.id,k.id>] + A[<j.id,k.id>] - (2 * X[<i.id,j.id,k.id>]) >= 0 ; 
			A[<i.id,k.id>] + A[<j.id,k.id>] - (2 * X[<i.id,j.id,k.id>]) <= 1 ;
		}	
  	}		  
}


// Equation 17

// C i,j / Ti <= Capacity utilization of node j
// ratio : wcet of function i on node j / period of i must be <= Capacity utilization of node j
// In order to constrain the nodes utilization


subject to {
	forall(j in nodeSet)
	  execution_node_constraining:
	  sum(i in functionSet) A[<i.id,j.id>] * wcetOfFunctionOnNodeSet[<i.id,j.id>]/ i.period <= j.capacity;
}


/**
  *sub-section 2 signals palcement
  *
  **/
  
  
  // Equation 18
  // AS binary variable to allocate or place each on one communication bus

subject to{
	forall( i in signalSet)
		remote_signal_placed_on_one_and_only_one_bus:
		sum(j in busSet) AS[<i.id,j.id>] ==  G[i.id];

}

//Equation 19

subject to{
	forall(i in signalSet){
		forall(j in i.rec : j != i.sen){
//			remote:
	  		1 - sum(k in nodeSet) X[<i.sen,j,k.id>] == G[i.id];
   		}	  		
 	}   
 }
 

// Equation 20


subject to {
	forall(i,j in signalSet : i.id != j.id ){
		forall(k in busSet){	
			Si_and_Sj_are_placed_on_the_same_bus_or_not :
			AS[<i.id,k.id>] + AS[<j.id,k.id>] - (2 * XS[<i.id,j.id,k.id>]) >= 0 ; 
			AS[<i.id,k.id>] + AS[<j.id,k.id>] - (2 * XS[<i.id,j.id,k.id>]) <= 1 ;
		}		
	}
}


//Equation 21

subject to {
	forall(i in signalSet, b in busSet){
		forall(j in i.rec){
		//topology		
			G[i.id] + sum(k in b.NB) A[<i.sen,k>] + sum(k in b.NB) A[<j,k>] - 3 * AS[<i.id,b.id>] >= 0;
			G[i.id] + sum(k in b.NB) A[<i.sen,k>] + sum(k in b.NB) A[<j,k>] - 3 * AS[<i.id,b.id>] <= 3;		
		}		
	}
}
	


// Equation 22


subject to {
	forall(j in busSet){
		execution_bus_constraining:
		sum(i in signalSet) AS[<i.id,j.id>] * wcetOfSignalOnBusSet[<i.id,j.id>]/ i.period <= j.capacity;
	}
}


/**
  * section 2 functions /signals partitioning and priority assignement
  **/

  
/**
  * sub-section 1 functions partitioning and priority assignment
  **/
  
  
  // Equation 23
  
  
subject to {

	forall( i,j in functionSet : i.id != j.id ){
		priority_order_for_function : 		
		Psi[<i.id,j.id>] + Psi[<j.id,i.id>] <= 1;		
	}
}
  
  //Equation 24 - 25 - 26 - 27 - 28 
  
subject to {

	forall( i,j,k in functionSet : i.id != j.id && j.id != k.id && i.id != k.id ){
//		 enforcing the cymmetric, transitive and inversion properties of the priority 
		Psi[<i.id,j.id>] + Psi[<j.id,k.id>] - 1 <= Psi[<i.id,k.id>];
		
//		Psi[<i.id,j.id>] >= 0 && Psi[<j.id,k.id>] >= 0 => Psi[<i.id,k.id>] >= 0 ;
//		
//		cym_trans_inv_functions : 
		Psi[<i.id,j.id>] - (Psi[<j.id,k.id>] + Psi[<k.id,j.id>]) <= Psi[<i.id,k.id>];
		Psi[<j.id,k.id>] - (Psi[<j.id,i.id>] + Psi[<i.id,j.id>]) <= Psi[<i.id,k.id>];
		Psi[<i.id,j.id>] + Psi[<j.id,i.id>] + Psi[<j.id,k.id>] + Psi[<k.id,j.id>] >= Psi[<i.id,k.id>];
		Psi[<i.id,j.id>] + Psi[<j.id,i.id>] + Psi[<j.id,k.id>] + Psi[<k.id,j.id>] >= Psi[<k.id,i.id>];		
	}
}

	// I have done some change on the following constraint
	// I changed the expression from i.period >= j.period to ===> j.period <= j.period
	
	// if it does't work i must set it back because it was mentioned >= in the asma's work


  // Equation 29

subject to { 
	
	forall(i,j in functionSet : i.id !=  j.id ){	
		if(i.period >= j.period && i.period % j.period != 0){
			Psi[<i.id,j.id>] + Psi[<j.id,i.id>] == 1 ;
		}

		//if(i.period < j.period /*&& i.period % j.period != 0*/){
		//	Psi[<i.id,j.id>]  == 1 ;
		//}

	}	
}


// Equation 30

// if dp(i,j) = 1 which means i depends on j then we force Psi = 0 (dp is a constant)

subject to {
 	forall(i,j in functionSet : i.id != j.id){
 		if(dp[<i.id,j.id>] == 1){
 			Psi[<i.id,j.id>] == 0;
 	 	} 	
 	}
}



/**
  * sub-section 2 signals partitioning and priority assignment
  *
  * in this sub-section, constraints for functions partionning are used for signals
  * for the same purpose
  *
  *******************
  *
  * the variables used are the same with an additional "S" to distinguish between
  * functions and signals
  *
  **/
  
  
  // Equations inspired from equations 23  to 28
  // to partition signals to messages and give them a priority order
  
 subject to {
 	forall(i,j in signalSet: i.id != j.id){
 		priority_order_for_signals : 	
		SPsi[<i.id,j.id>] + SPsi[<j.id,i.id>] <= 1;	
 	}
 }
  
subject to {

	forall( i,j,k in signalSet : i.id != j.id && j.id != k.id && i.id != k.id ){
//		 enforcing the cymmetric, transitive and inversion properties of the priority 
		SPsi[<i.id,j.id>] + SPsi[<j.id,k.id>] - 1 <= SPsi[<i.id,k.id>];
		SPsi[<i.id,j.id>] - (SPsi[<j.id,k.id>] + SPsi[<k.id,j.id>]) <= SPsi[<i.id,k.id>];
		SPsi[<j.id,k.id>] - (SPsi[<j.id,i.id>] + SPsi[<i.id,j.id>]) <= SPsi[<i.id,k.id>];
		SPsi[<i.id,j.id>] + SPsi[<j.id,i.id>] + SPsi[<j.id,k.id>] + SPsi[<k.id,j.id>] >= SPsi[<i.id,k.id>];
		SPsi[<i.id,j.id>] + SPsi[<j.id,i.id>] + SPsi[<j.id,k.id>] + SPsi[<k.id,j.id>] >= SPsi[<k.id,i.id>];
	}
}


// I have commented the following constraint because I think it was the one which affected my results
// priority problems


// Equation 31


subject to {
	
	forall(i,j in functionSet, k in nodeSet : i.id != j.id){
		functions_placed_on_same_nodes_and_i_has_priority_lower_than_j : 
		X[<i.id,j.id,k.id>] + Psi[<j.id,i.id>] - (2 * SnHp[<i.id,j.id,k.id>]) >= 0;
		X[<i.id,j.id,k.id>] + Psi[<j.id,i.id>] - (2 * SnHp[<i.id,j.id,k.id>]) <= 1;
	}
}

// Equation 32

subject to {
	
	forall(i,j in functionSet, k in nodeSet : i.id != j.id){
		functions_placed_on_same_nodes_and_partitioned_on_different_tasks : 
		SnDp[<i.id,j.id,k.id>] == SnHp[<i.id,j.id,k.id>] + SnHp[<j.id,i.id,k.id>] ;
	}
}


//subject to {
////	forall(i,j in functionSet, k in nodeSet:i.id != j.id ){
////	  if(i.id == 1 && j.id == 2 && k.id == 1){
//		SnSp[<1,2,1>] == 0;
////	}		
////	}		
//}


 // Equation 33

subject to {
	
	forall(i,j in functionSet, k in nodeSet : i.id != j.id){
		functions_placed_on_same_nodes_and_partitioned_on_same_tasks : 
		SnSp[<i.id,j.id,k.id>] + SnDp[<i.id,j.id,k.id>] == X[<i.id,j.id,k.id>];

		//(X[<i.id,j.id,k.id>] == 1) => (SnSp[<i.id,j.id,k.id>] != SnDp[<i.id,j.id,k.id>]) ;

	}
}

 // equation 34

// in the following constraints there is a problem 
// I need to isolate the l the current node
		
		subject to {
		
		 	forall(i  in signalSet, l in nodeSet, j,k in i.rec : j != k){		
		 	 	    	sum(l in nodeSet) SnSp[<i.sen,j,l.id>] == sum(l in nodeSet) SnSp[<i.sen,k,l .id>];
			}    	    
		}
/*subject to {
forall( c in nodeSet, i in signalSet, k,r in i.rec: k!= r){
       SnSp[<i.sen,k,c.id>] == sum(l in nodeSet)SnSp[<i.sen,r,l.id>];
}

}*/

// Equation 35

subject to{
	forall(i,j in signalSet : i.id != j.id && i.sen != j.sen )
	  sum(k in nodeSet) X[<i.sen,j.sen,k.id>] >= sum(l in busSet) SnSpS[<i.id,j.id,l.id>];

}

/**
  * section 3 functions / signals WCRT computation
  **/
  
/**
  * sub-section 1 functions WCRT computation 
  **/
  
  // Equation 36

 subject to {
 	forall(i in functionSet)
 	  WCRT_computation : 
 	  R[i.id] == W[i.id] + J[i.id];
 }
 
 // Equation 37 - 38
 
 subject to {
 	forall(i,j in functionSet : i.id != j.id){
        Sigma[<i.id,j.id>] -( W[i.id] + J[j.id]) / j.period >= 0 ;
 	 	Sigma[<i.id,j.id>] -( W[i.id] + J[j.id]) / j.period <= 1 - EPS ;
 	}
 }
 
 // Equation 39 40 41
 
 subject to {
 	forall(i,j in functionSet, k in nodeSet : i.id  != j.id){
 	worst_case_number_of_interf_fj_on_fi_within_Ck:

 	 	Sigma[<i.id,j.id>] - BIG_M * (1 - SnHp[<i.id,j.id,k.id>]) <= I[<i.id,j.id,k.id>];	
 	 	I[<i.id,j.id,k.id>] <= Sigma[<i.id,j.id>];
 		I[<i.id,j.id,k.id>] <= BIG_M * SnHp[<i.id,j.id,k.id>];
 	}
 }
 
 // Equation 42
 
 subject to  {
 	
 	forall(i in functionSet){
 	completion_time_W_of_a_function: 	
 	
 		W[i.id] == sum (k in nodeSet) A[<i.id,k.id>] * (wcetOfFunctionOnNodeSet[<i.id,k.id>] + 2 * CONTEXT_SWITCH_COST)
 		+ sum( j in functionSet, k in nodeSet : j.id != i.id)	SnSp[<i.id,j.id,k.id>] * wcetOfFunctionOnNodeSet[<j.id,k.id>]
 		
 		// in case Xi = 1 
		+ sum(j in functionSet, k in nodeSet : j.id != i.id ) Xi[<i.id,j.id>] * I[<i.id, j.id, k.id>] * (wcetOfFunctionOnNodeSet[<j.id,k.id>] + 2 * CONTEXT_SWITCH_COST);
 	}	 
 }
 
 // Equation 43

 subject to{
 	forall(j in signalSet, i in j.rec){
 	
 	// I have made a modification here bellow the original was 	
 		// Phi[i] >= R[j.id];
 	 // the modification is as follows
 	 
 	 //Phi[i] >= maxl(RS[j.id]);
 	 Phi[i] >= RS[j.id];//Ant
 	/*  Phi[i] >= max(0, RS[j.id]);
 	  
 	 Phi[i] >= max(j in signalSet) RS[j.id]);
 	 
 	 maxl(0, max(I in possibleEmptySet) dd[i])*/
 	 
	} 	
 }

// Equation 44

subject to {
	forall(i,j in functionSet : i.id != j.id){
	  Phi[j.id] - BIG_M * ( 1 - sum(k in nodeSet) SnSp[<i.id,j.id,k.id>]) <= Theta[<i.id,j.id>];
 	}	  
}

// Equation 45

subject to {
	forall(i,j in functionSet : i.id != j.id){
	  Theta[<i.id,j.id>] <= Phi[j.id];
 	}	  
}

// Equation 46

subject to {
	forall(i,j in functionSet : i.id != j.id){
	  Theta[<i.id,j.id>] <= BIG_M * ( sum(k in nodeSet) SnSp[<i.id,j.id,k.id>]);	  
 	}	  
}

// Equation 47

subject to{
	forall(i,j in functionSet: i.id != j.id){
		J[i.id] >= Theta[<i.id,j.id>];	
	}
}

/**
  * sub-section 2 signals WCRT computation 
  **/
  
  // Equation 48

subject to {
	forall( i in signalSet ){
	  
	  RS[i.id]  == 	WS[i.id] + sum(k in busSet) AS[<i.id,k.id>] * wcetOfSignalOnBusSet[<i.id,k.id>] +  sum (j in signalSet, k in busSet : j.id != i.id)SnSpS[<i.id,j.id,k.id>] * wcetOfSignalOnBusSet[<j.id,k.id>] + JS[i.id]; 
     
      }	  					
}



subject to {
	forall(i,j in signalSet : i.id != j.id){
	  SigmaS[<i.id,j.id>] - (WS[i.id] + JS[j.id]) / j.period >= 0;
	  SigmaS[<i.id,j.id>] - (WS[i.id] + JS[j.id]) / j.period <= 1 - EPS;
	}	  
}


/** Equations deduced from formula 38 **/

subject to {
	forall(i,j in signalSet, k in busSet : i.id != j.id){
		SigmaS[<i.id,j.id>] - BIG_M * (1 - SnHpS[<i.id,j.id,k.id>]) <= IS[<i.id,j.id, k.id>];
	}
}



subject to {
		forall(i,j in signalSet, k in busSet : i.id != j.id){
		IS[<i.id,j.id,k.id>] <= SigmaS[<i.id,j.id>];
	}
}

subject to {
	forall(i,j in signalSet, k in busSet : i.id != j.id){
		IS[<i.id,j.id,k.id>] <= BIG_M * SnHpS[<i.id,j.id,k.id>];
	}
}

/***************************************/

 // Equation 50 - 1
subject to {
	forall(i,j in signalSet , k in busSet : i.id != j.id){
		BS[i.id] >=  SnHpS[<j.id,i.id,k.id>] * wcetOfSignalOnBusSet[<j.id,k.id>]
			+ sum(l in signalSet : l.id != i.id && l.id != j.id) SnSpS[<j.id,l.id,k.id>] * wcetOfSignalOnBusSet[<l.id,k.id>];	
		
	}

}



 // Equation 50 - 2

subject to {
	forall(i in signalSet)
	  BS[i.id] >= sum(j in signalSet, k in busSet : i.id != j.id) SnSpS[<i.id,j.id,k.id>] * wcetOfSignalOnBusSet[<j.id,k.id>];

}

 // Equation 51

subject to {
	forall(i in signalSet)
	  WS[i.id] == BS[i.id]
	  
	  // signal i and j are concurrent
	  + sum(j in signalSet, k in busSet : i.id != j.id) Xis[<i.id,j.id>] * IS[<i.id,j.id,k.id>] * wcetOfSignalOnBusSet[<j.id,k.id>];
}

	/**** Alpha inter-task comm  ****/


 // Equation 54
	
subject to {
	forall(i in signalSet, j in i.rec : i.sen != j ){
	 		R[i.sen] - BIG_M * (1 - sum(k in nodeSet)SnDp[<i.sen,j,k.id>]) <= Alpha[i.id];	
	 } 	 	
}

subject to {
	forall(i in signalSet)
	  Alpha[i.id] <= R[i.sen];
}

subject to {
	forall(i in signalSet, j in i.rec  : i.sen != j)
	  Alpha[i.id] <= BIG_M *  sum(k in nodeSet ) SnDp[<i.sen,j,k.id>];
}


 // Equation 55

//	/**** Zeta intra-task comm  ****/
	

subject to {
	forall(i in signalSet, j in i.rec : i.sen != j){
	  J[i.sen] - BIG_M * (1 - sum(k in nodeSet )SnSp[<i.sen,j,k.id>]) <= Zeta[i.id];
	  Zeta[i.id] <= J[i.sen];
	  Zeta[i.id] <= BIG_M * sum(k in nodeSet )SnSp[<i.sen,j,k.id>];
 	}	  
}   

 // Equation 56

//jitter of local signal

subject to {
	forall(i in signalSet){
		JS[i.id] >= Alpha[i.id] + Zeta[i.id];
	}
}


 // Equation 57

	/**** Lamda remote comm ****/
// jitter of remote signal


subject to {

	forall(i,j in signalSet, k in busSet : i.id != j.id){
		JS[i.id] >= Lamda[<i.id,j.id,k.id>];	
	}		
}

// Equation 59

subject to {
	forall(i,j in signalSet, k in busSet : i.id != j.id){
		R[j.sen] - BIG_M * (1 - SnSpS[<i.id,j.id,k.id>]) <= Lamda[<i.id,j.id,k.id>];
	}	
}

// Equation 60

subject to {
	forall(i,j in signalSet, k in busSet : i.id != j.id){
		Lamda[<i.id,j.id,k.id>] <= R[j.sen] ;
	}	
}

 // Equation 61

subject to {
	forall(i,j in signalSet, k in busSet : i.id != j.id){
		Lamda[<i.id,j.id,k.id>] <= BIG_M * SnSpS[<i.id,j.id,k.id>];
	}	
}


/**
  * section 4 timing constraints
  **/
  
  // in this section, we calculate the WCRT ('R') for each function/signal and path 
  
  
 // Equation 62
  
 subject to{
 	forall(i in pathSet){
 		L[i.id] == R[i.sink];
 	}
 }
 
  // Equation 63
 
 subject to{
 	forall(i in pathSet){
 		L[i.id] <= i.deadline; 	
 	} 
 }
 
 
 /**
  * the section bellow is devoted to test every dataSet 
  * that are used in the program above to solve the problem
  **/
 
// 
//   execute {
//  
//  	for(var i in graph)
//  		writeln("path number : " + i.id + "\tpath components : "+i.components );
//    
//  }
 
//execute {
// 	writeln(wcetOfFunctionOnNodeSet[FunctionPlacementPossibilitySet.find(2,1)]);
//
//	for (var v in FunctionPlacementPossibilitySet)
//		write(v);
//		
//	for (var v in placementInSameNodePossibilitySet)
//		write(v);
//	
//
//	
//	for (var v in wcetOfFunctionOnNodeSet)
//		write(wcetOfFunctionOnNodeSet[v]+"\t"+" v : " + v + "\n" );
//		
//	
//
//for (var v in functionSet)
//		write("f["+v+"] = " + v.period + "\n");
//
////	for(var v in wcetOfFunctionOnNodeSet)
////		write(wcetOfFunctionOnNodeSet[<1,2>])
////	
//}


 
