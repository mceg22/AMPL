#----------------------------------------------------------------------------------------------------
#OBJECTIVE FUNCTION DEFINITION

#We have to decide what will be our objective. We want to model delays.
#We have to specify what is considered a delay

#First of all, each order will have a number of objects:
param TotalDemand{k in Orders} := card{(i,j,l) in Objects: l=k} integer, >0;

#The following variable denotes the units of order k already delivered in a day:
var TotalDelivered{k in Orders,t in DeliveryPeriod[k]} =
											 sum{(i,j,l) in Objects: l=k} Delivered[i,j,l,t];

#From them, we define the following variables, which tell if an order is already finished a day:
var Finished{k in Orders, DeliveryPeriod[k]} binary;

#If this variable is 0, then the demand has been satisfied:
s.t. Control_Restriction_Finished1{k in Orders, t in Time}:
	TotalDelivered[k,t] >=  TotalDemand[k]*(1-Finished[k,t]);

#If this variable is 1, then the demand is not yet satisfied:
s.t. Control_Restriction_Finished2{k in Orders, t in Time}:
	TotalDemand[k] - TotalDelivered[k,t] >=  1*Finished[k,t];

#Although it is not necessary, we would like to know how many delay has happened for each order:
var Delay{k in Orders} = sum{t in DeliveryPeriod[k]} Finished[k,t];



#We tell the different periods in which we divide the delay time:
param num_Delay_MiniPeriods integer, > 0;
set DelayMiniPeriods = 1..num_Delay_MiniPeriods;
param days_MiniPeriods{k in Orders} := ceil((ord(Day_Finish[k], Time)-ord(Day_Lim[k],Time))
										/num_Delay_MiniPeriods);


#We define the whole delay period and divide it by the different mini-periods:
set DelayPeriod{k in Orders} = {t in Time: ord(t,Time) > ord(Day_Finish[k],Time)
								and ord(t,Time) <= ord(Day_Lim[k],Time)} ordered by Time; 

set DelayMiniPeriod{k in Orders, m in DelayMiniPeriods} = {t in DelayPeriod[k]:
				ord(t,DelayPeriod[k])-1>=days_MiniPeriods[k]*(m-1) and
				ord(t,DelayPeriod[k])-1<=days_MiniPeriods[k]*m};



#We define the objective function as the sum of delays, but weighted by the an incresaing
#constant depending on the delay period they are in. We want to minimize it:
minimize PonderedSumDelays: sum{k in Orders, m in DelayMiniPeriods, t in DelayMiniPeriod[k,m]}
							Finished[k,t]*10*m;


			
			
