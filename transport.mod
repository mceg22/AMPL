# TRANSPORT CONSTRAINTS AND SPECIFIC PARAMETERS

#Sets of vehicles avalaible for delivering products. Some of them are smaller and there are products that can't be carried on them.
set Vehicles;
set Small_Vehicles within Vehicles;

#-----------------

#Limit of loops that can be done in one day
param TravelLimit integer;

#------------------

#Set of loops that can be done in one day
set Loops := {1..TravelLimit};

#------------------

#Maximum height/width of an object that can be delivered in a small vehicle
param LittleCap;

#Each vehicle can carry a number of units because we are considering that every product is as thick as the rest, so they can be put in a 
#row one before another, whichn allow us to only count the number of products.
param Capacity_Vehicle{Vehicles};

#------------------

var Transport;

var Use_Loop;

#------------------
	
# No se puede superar la capacidad del camion en cada viaje
s.t. Vehicle_Capacity_Per_Loop{t in Delivery_Days, u in Vehicles, s in Loops}:
	sum{k in Orders, j in Products[k], i in Objects[k,j]: t in Delivery_Period[k]} Transport[k,j,t,i,u,s] <= Capacity_Vehicle[u];

# Tambien hay vehiculos que son muy pequennos para llevar ciertos objetos
s.t. Small_Vehicles_Restriction{u in Small_Vehicles, s in Loops, k in Orders, j in Products[k], i in Objects[k,j]: Cap[k,j,i] >= LittleCap}:
	sum{t in Delivery_Days inter Delivery_Period[k]}Transport[k,j,t,i,u,s] = 0;

# Las variables binarias de uso de los viajes deben representar lo que buscamos
# Para ello vamos a poner una restricion que nos asegura que si se envia algo a la empresa 
# k en el viaje s, entonces la variables binaria debe de activarse
# Para ello usamos una M-grande, el valor para esa M-grande es la suma de todas las demandas
# de ese pedido
s.t. Control_Restriction_Use_Loop1{u in Vehicles, s in Loops, k in Orders, t in Delivery_Days inter Delivery_Period[k]}:
	sum{j in Products[k], i in Objects[k,j]}Transport[k,j,t,i,u,s] <= Use_Loop[k,t,u,s]*(sum{r in Orders, v in Products[r]}Demand[r,v]);

# El problema es el siguiente y es que puede darse el caso de que la variables binaria 
# Use_Loop, se active por cualquier razon lo cual puede afectar de cara a la suma de los
# tiempos, habria que plantearse si es necesario introducir una nueva familia de restricciones
# para linealizar la implicacion reciproca

# Hay que restringuir que solo se puede dedicar cada viaje a una empresa, a lo sumo
s.t. One_Order_Per_Loop{t in Production_Days, u in Vehicles, s in Loops}:
	sum{k in Orders: t in Delivery_Period[k]}Use_Loop[k,t,u,s] <= 1;
	
# Ahora annadimos la restriccion de tiempo de trabajo para el reparto
s.t. Delivery_Work_Time_Limitation{t in Delivery_Days, u in Vehicles}:
	 sum{k in Orders, s in Loops: t in Delivery_Period[k]}Delivery_Time[k]*Use_Loop[k,t,u,s] <= H;

