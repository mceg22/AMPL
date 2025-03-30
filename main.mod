#-------------------------------------------------------------------------------------------------
#BASIC PRODUCTION MODEL

/*The problem consists on deciding which day to produce each object and which day to send it.
This time is limited by the days we can produce, the days we can transport them and the time
we have to do each of these days.*/






#Production is controlled by time. But we only produce in non-festive days:
set Time ordered;
set Holidays ordered by Time;
set ProductionDays ordered by Time = Time diff Holidays;

#Also, we can only trasnport some of these production days:
set DeliveryDays ordered by ProductionDays;


#We have different objects to produce. They come in orders. Each order has to produce different
#objects of the same time:
set Objects dimen 3;
set Orders = setof{(i,j,k) in Objects} k;
set ProductTypes = setof{(i,j,k) in Objects} j;
set Units = setof{(i,j,k) in Objects} i;




#We state the days when the orders can start to be delivered, the dates where they should finish and
#the limit date where a delay is allowed: 
param Day_Begin{Orders} in ProductionDays;
param Day_Finish{Orders} in ProductionDays;
param Day_Lim{Orders} in ProductionDays;

#Then, the days when an order is able to be delivered are:
set DeliveryPeriod{k in Orders} = {t in Time: ord(t,Time)>=ord(Day_Begin[k],Time)
								and ord(t,Time) <=ord(Day_Lim[k],Time)} ordered by Time;
set ConcreteDeliveryDays{k in Orders} = DeliveryDays inter DeliveryPeriod[k] ordered by Time;
			


#-------------------------------------------------------------------------------------------------
#VARIABLES:

#The main variable is 1 if we fabricate an object in a specific day (0 if not):
var Produce{Objects, ProductionDays} binary;

#This second one is 1 if an object is delivered in a specific dat (0 if not):
var Deliver{(i,j,k) in Objects, ConcreteDeliveryDays[k]} binary;

#From this one we can construct another that tells if the demand of an object will be satified a day:
var Delivered{(i,j,k) in Objects, t in DeliveryPeriod[k]} =
			sum{s in ConcreteDeliveryDays[k]: ord(s,DeliveryPeriod[k])<=ord(t,DeliveryPeriod[k])}
			Deliver[i,j,k,s];

#We can also define a variable that tells if an object is stored someday:
var Stored{Objects, ProductionDays} binary;



#--------------------------------------------------------------------------------------------------
#CONSTRAINTS:

#An object can only be produced once:
s.t. Once_Produced{(i,j,k) in Objects}: sum{t in ProductionDays} Produce[i,j,k,t] =1;

#An object can only be delivered once:
s.t. Once_Delivered{(i,j,k) in Objects}: sum{t in ConcreteDeliveryDays[k]} Deliver[i,j,k,t] =1;

#An object is stored when it is produced, but it is not still stored when it is delivered:
s.t. Once_Stored{t in ProductionDays, (i,j,k) in Objects}:
		Stored[i,j,k,t] = (if t=first(ProductionDays) then 0 else Stored[i,j,k,prev(t)]) +
		Produce[i,j,k,t] - (if t not in ConcreteDeliveryDays[k] then 0 else Deliver[i,j,k,t]);

#We suppose an object cannot be delivered until the day after it is produced:
s.t. Produce_before_Deliver{(i,j,k) in Objects, t in ConcreteDeliveryDays[k]}:
		Deliver[i,j,k,t] <= sum{s in ProductionDays: ord(s,ProductionDays) < ord(t,ProductionDays)}
							Produce[i,j,k,s];

	
#These were obviuos constraints for our model
#The next additional constraint limits the production per day:

param WorkTimeDay{ProductionDays} > 0;	#Working time per day
param CostTime{ProductTypes} > 0;	#Time needed to produce a kind of product

s.t. Production_Work_Time_Limitation{t in ProductionDays}:
	sum{(i,j,k) in Objects} CostTime[j]*Produce[i,j,k,t]<= WorkTimeDay[t];




#We already have defined the main model. To complement it we need to add an objective function
#and the additional constraints we woud like to consider: storage, raw materials, transportation...
	 













