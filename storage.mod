/*--------------------------------------------------------------------------------------------------
----STORAGE

In this file, we limit the storage of produced materials. We decide how we store them.

The products will be stored in carts: we have some carts with their own length measures.
Their depth is little, so we cannot place one object on top of another. Thery are disposed in a row.
Objects can be placed vertical and horizontal (we will choose the smallest side).
We place them in the row without esceeding the length of the cart.*/



#Set of carts:
set Carts;

#Number of carts, in case Carts is defined by the number of carts:
param NumCarts integer, >0;
check card(Carts)=NumCarts;

#Their length:
param StorageCapacity{Carts} >0;
#In case all of them have the same capacity:
param CartsCapacity >0; 								




#We define a variable that tells us in which cart a produced object is situated when stored.
#It takes the value 1 if the object is stored in the cart said in the day said:
var Storage{Objects, ProductionDays, Carts} binary;





#The first constraint to add is that if an object is stored in some cart, it is considered
#stored in the warehouse. Because Stored is binary, this constraint also tells that each
#object is stored in just a cart each day: 
s.t. Total_Storing{(i,j,k) in Objects, t in ProductionDays}:
						sum{c in Carts}	Storage[i,j,k,t,c] = Stored[i,j,k,t];


#We also want to limit the use of carts. When an object is stored in one, it does not change the cart
#any other day:
s.t. Unique_Cart{(i,j,k) in Objects, c in Carts, t in ProductionDays: t != first(ProductionDays)}:
						Storage[i,j,k,t,c] = Storage[i,j,k,prev(t),c];


#We finally state that the objects stored in each cart cannot exceed their capacity:
param CartVolume{Objects} >0;
s.t. Cart_Capacity{t in ProductionDays, c in Carts}:
	sum{(i,j,k) in Objects}Storage[i,j,k,t,c]*CartVolume[i,j,k] <= StorageCapacity[c];
	
	
	
	
	
