# RESTRICCIONES DE TRANSPORTE

# Cada objeto solo se transporta una vez
s.t. Unique_Delivery1{k in Orders, j in Products[k], i in Objects[k,j]}:
	sum{t in Delivery_Days inter Delivery_Period[k], u in Vehicles, s in Loops}Transport[k,j,t,i,u,s] = 1;

# Para que la variable Delivered signifique lo que queremos
s.t. Unique_Delivery2{k in Orders, j in Products[k], t in Production_Days, i in Objects[k,j]}:
	sum{u in Vehicles, s in Loops, r in Delivery_Period[k] inter Delivery_Days: r <= t}Transport[k,j,r,i,u,s] = Delivered[t,k,j,i];
	
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

#Restriccion para que cada vehiculo no haga mas del maximo de viajes

s.t. Max_Loops{t in Delivery_Days, u in Vehicles}:
	sum{k in Orders, s in Loops} Use_Loop[k,t,u,s] <=L;
