# Primero los parametros para el numero de dias y el numero de pedidos 
param T integer;
param k integer;

# Ahora vamos a definir los conjuntos
set Pedidos:={1..k};
set Producto{Pedidos};
