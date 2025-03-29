# ----------------------------------------------------------------------------------
# PARAMETROS NUMERICOS

# Horas de trabajo disponible
param H integer;

# Necesitamos conocer el numero de viajes que puede hacer cada vehiculo
param L;

# El numero de cajones o carritos donde se puede almacenar los productos
param C;
# Capacidad de cada carrito
param Storage_Capacity;

# Sera el umbral para meter o no cosas en el camion pequenno, es decir, mas adelante 
# definiremos un parametro que sera Cap, que nos dira el maximo entre el alto y el 
# ancho de cada objeto, si ese Cap supera a LittleCap ese objeto no puede ir en vehi-
# culos pequennos
param LittleCap;

# La idea es que para cada semana el gasto de materias primas esta limitado para evitar
# poner un 5 fijamos un parametro que nos dice la duracion o longitud del periodo
param Period integer;

# ----------------------------------------------------------------------------------
# CONJUNTOS

# El conjunto de los pedidos
set Orders;

# Para cada pedidos tenemos un conjunto de productos
set Products{Orders};

# Conjunto de vehiculos
set Vehicles;
set Small_Vehicles within Vehicles;

# El conjunto de materias primas
set RawMaterials;

# El conjunto de los dias que hay reparto
set Production_Days ordered;
set Delivery_Days within Production_Days;

# -------------------------------------------------------------------------------
# PARAMETROS

# Las demandas de cada tipo de objeto
param Demand{k in Orders,Products[k]};
param Total_Demand{k in Orders}:=sum{j in Products[k]}Demand[k,j];

# El tiempo que se tarda en construir cada tipo de objeto
param Cost_Time{k in Orders, j in Products[k]};

# Coste de materias primas de cada tipo de objeto
param Cost_RawMat{k in Orders, j in Products[k], l in RawMaterials};

# Capacidad de almacenamiento para cada materia prima
param Limitation_Use_Material{RawMaterials};

# El numero de unidades que caben en cada vehiculo (porque lo hacemos en unidades y no en volumen)
param Capacity_Vehicle{Vehicles};

# Tiempo que tarda un vehiculo en ir de la fabrica a la empresa k
param Delivery_Time{Orders};

# Los dias de inicio de la entrega
param Day_Begin{Orders};
# Los dias de supuesta finalizacion
param Day_Finish{k in Orders};
# Los dias limite para cada pedido
param Day_Lim{k in Orders};
# La fecha donde acaba el primer periodo
param Day_Period1{k in Orders};
param Day_Period2{k in Orders};

# Penalizacion en el periodo 1
param Penalty1{Orders};
# Penalizacion en el periodo 2
param Penalty2{Orders};
# ----------------------------------------------------------------------------------#
#Conjunto de objetos de un tipo en un pedido
set Objects{k in Orders, j in Products[k]}:= {1..Demand[k,j]};
#Conjunto de viajes que se pueden hacer en un dia
set Loops := {1..L};
#Conjunto de dias en los que se puede mandar algo a la empresa k
set Delivery_Period{k in Orders} := {t in Production_Days: ord(t,Production_Days) >= ord(Day_Begin[k], Production_Days) and ord(t,Production_Days) <= ord(Day_Lim[k], Production_Days)};
# ----------------------------------------------------------------------------------
# ----------------------------------------------------------------------------------
# Parametros de medidas de cada objeto
param Height{k in Orders, j in Products[k], i in Objects[k,j]};
param Width{k in Orders, j in Products[k], i in Objects[k,j]};

# El siguiente parametro guardara el maximo entre la altura y la anchura de cada objeto
param Cap{k in Orders, j in Products[k],i in Objects[k,j]}; 
# Luego en el .dat seleccionaremos con un for el maximo
# ----------------------------------------------------------------------------------
# VARIABLES DE DECISION

# --- VARIABLES DE PRODUCCION ---
# Las variables para saber si el objeto numero i de tipo j del pedido k se fabrica el
# dia t
var Production{t in Production_Days, k in Orders, j in Products[k], Objects[k,j]} binary;

# -------------------------------
# --- VARIABLES DE ALMACENAJE ---

# Las variables para saber en que cajon se almacena cada objeto en cada dia
var Storage{t in Production_Days, k in Orders, j in Products[k], Objects[k,j], 1..C } binary;

# Luego otra variables para saber si un cierto objeto esta almacenado un cierto dia
var Stored{t in Production_Days, k in Orders, j in Products[k], Objects[k,j]} binary;

# -------------------------------
# --- VARIABLES DE TRANSPORTE ---
# Variables de transporte para saber si el producto numero i de tipo j del pedido k
# se entrega el dia i en el viaje s-esimo del vehiculo u
var Transport{k in Orders, j in Products[k], Delivery_Days inter Delivery_Period[k], Objects[k,j], Vehicles, Loops} binary;

# Otra variable binaria para saber si un objeto ha sido entregado o no, es decir
# Delivered[t,k,j,i] = 1 si y solo si el dia t el objeto i de tipo (k,j) ya ha sido entre-
# gado el dia t, es decir, en alguno de los dias anteriores a t el objeto i ya ha sido en-
# tregado
var Delivered{t in Production_Days, k in Orders, j in Products[k], Objects[k,j]} binary;

# Vamos a necesitar un conjunto de variables extra para llevar la cuenta de los objetos
# de cada pedidos que han sido entregados hasta un cierto dia
# La idea es que Total_delivered = numero de objetos del pedido k que han sido entregados
# hasta el dia t, es por eso que t varia en todos los dias
var Total_Delivered{t in Production_Days, k in Orders} integer;

# Variables binaria para saber a que empresa se dedica el viaje s del vehiculo u en el
# dia k. Sera 1 si el viaje s del vehiculo u del dia i se dedica a la empresa k
var Use_Loop{k in Orders, Delivery_Days inter Delivery_Period[k], Vehicles, Loops} binary;

# --------------------------------
# --- PEDIDO DE MATERIALES ---
# Variables para el pedido de las materias primas
var Order_Materials{t in Production_Days, l in RawMaterials} integer;

# --- VARIABLES PARA LOS RETRASOS ---
# Las siguientes variables binarias seran 1 si y solo si el dia i no se ha terminado 
# de entregar en pedido k
var Finished{k in Orders, Day_Finish[k]..Day_Lim[k]} binary;
# ----------------------------------------------------------------------------------
# ----------------------------------------------------------------------------------

# ----------------------------------------------------------------------------------
# ----------------------------------------------------------------------------------
# RESTRICCIONES

# Restricciones de fabricacion cada objeto se fabrica una sola vez
s.t. Uniqueness{k in Orders, j in Products[k], i in Objects[k,j]}:
	sum{t in Production_Days}Production[t,k,j,i] = 1;

# Restriccion de horas de trabajo
s.t. Production_Work_Time_Limitation{t in Production_Days}:
	sum{k in Orders, j in Products[k], i in Objects[k,j]}Cost_Time[k,j]*Production[t,k,j,i] <= H;


# ----------------------------------------------------------------------------------
# RESTRICCIONES DE ALMACENAJE
s.t. Capacity{t in Production_Days, c in 1..C}:
	sum{k in Orders, j in Products[k], i in Objects[k,j]}Storage[t,k,j,i,c] <= Storage_Capacity;

# Para que las variables de almacenaje representen lo que queremos
s.t. Storing1{t in Production_Days, k in Orders, j in Products[k], i in Objects[k,j]}:
	sum{c in 1..C}Storage[t,k,j,i,c] = Stored[t,k,j,i];

s.t. Storing2{t in Production_Days, k in Orders, j in Products[k], i in Objects[k,j]}:
	1 >= Stored[t,k,j,i];
# ----------------------------------------------------------------------------------
# La siguiente familia de restricciones es para relacionar la produccion el reparto
# y el almacenaje
s.t. Store_Deliver_Prodc{t in Production_Days, k in Orders, j in Products[k], i in Objects[k,j]}:
	 Stored[t,k,j,i] + Delivered[t,k,j,i] <=1;

s.t. Store_Deliver_Prodc2{t in Production_Days, k in Orders, j in Products[k], i in Objects[k,j]}:
	 Stored[t,k,j,i] + Delivered[t,k,j,i] >= Stored[t-1,k,j,i] +Production[t,k,j,i]; 
# ----------------------------------------------------------------------------------
# RESTRICCIONES GASTO DE MATERIAS PRIMAS

# El uso de materias primas esta limitado por semana, la longitud de la semana (periodo de tiempo
# cualquiera) lo marca el parametro Period
# member(n,A) devuelve el miembro n-esimo del conjunto ordenado A
s.t. Material_Limitation_Use{l in RawMaterials, t in 1..card(Production_Days) by Period}:
	sum{r in 0..Period-1, k in Orders, j in Products[k], i in Objects[k,j]}Cost_RawMat[k,j,l]*Production[member(t+r,Production_Days),k,j,i] <= Limitation_Use_Material[l];
# ----------------------------------------------------------------------------------
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

# ----------------------------------------------------------------------------------
# MODELIZAR LOS RETRASOS
# ----------------------------------------------------------------------------------
# Vamos ahora con la modelizacion como se contabilizan los dias de retraso
# La razon de hacerlo lo ultimo es debido a que todo lo demas es la base a partir de la cual
# veremos como contabilizar los dias que se tarda en entregar uno de los pedidos

# Primero es que la variable Total_Delivered represente lo que buscamos es decir, la variable
# Total_Delivered lleva la cuenta de las unidades del pedido k que se ha entregado hasta el 
# dia t
s.t. Already_Delivered{t in Production_Days, k in Orders}:
	sum{j in Products[k], i in Objects[k,j], u in Vehicles, s in Loops, r in Delivery_Days inter Delivery_Period[k]: r<=t}Transport[k,j,r,i,u,s] = Total_Delivered[t,k];
	
# Introducimos unas nuevas variables bianrias que nos digan si el dia i es de retraso
# para el pedido k, pero eso hay que expresar en forma de restricciones
# Vamos a necesitar variables binarias auxiliares que por facilidad definiremos aqui
# Ademas de parametros auxilizares como una M-grande una m_pequenna y un epsilon

var Aux1{k in Orders, Day_Begin[k]..Day_Lim[k]} binary;
var Aux2{k in Orders, Day_Begin[k]..Day_Lim[k]} binary;

param M;
param m;
param epsilon;

s.t. Control_Restriction_Finished1{k in Orders, t in Delivery_Period[k]}:
	Total_Delivered[t,k] <=  Total_Demand[k] + M*Finished[k,t];
	
s.t. Control_Restriction_Finished2{k in Orders, t in Delivery_Period[k]}:
	Total_Delivered[t,k] <=  Total_Demand[k] + m*Finished[k,t];

s.t. Control_Restriction_Finished3{k in Orders, t in Delivery_Period[k]}:
	Total_Delivered[t,k] >=  Total_Demand[k] + epsilon +  (m - epsilon)*Aux1[k,t];

s.t. Control_Restriction_Finished4{k in Orders, t in Delivery_Period[k]}:
	Total_Delivered[t,k] >=  Total_Demand[k] - epsilon +  (M + epsilon)*Aux2[k,t];

s.t. Control_Restriction_Finished5{k in Orders, t in Delivery_Period[k]}:
	Aux1[k,t] + Aux2[k,t] <= Finished[k,t];

# -------------------------------------------------------------------------------
# Entonces para contar el retraso debemos sumar las variables binarias que acabamos
# de definir pues con las restricciones que hemos annadido ya sabemos que reflejan 
# lo que buscamos
# De cara a cuando obtengamos la solucion nos gustaria poder rescatar cuanto retraso
# ha habido en cada reparto, es por eso que vamos a definir unas variables para con-
# tabilizarlo de forma mas directa
var Delay{Orders};
s.t. Counting_Delay_Days{k in Orders}:
	Delay[k] = sum{t in Delivery_Period[k]}Finished[k,t];

# -------------------------------------------------------------------------------
minimize Weighted_Delay_Sum:
	sum{k in Orders}(sum{t in Day_Finish[k]..Day_Period1[k]}Finished[k,t] + 
	sum{t in (Day_Period1[k] + 1)..Day_Period2[k]}Penalty1[k]*Finished[k,t] + 
	sum{t in (Day_Period2[k] + 1)..Day_Lim[k]}Penalty2[k]*Finished[k,t]);
