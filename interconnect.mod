#In this .mod we interconnect all of our models:

#We define TIME:
#We define our time interval, tha days from the beggining (today) till the period established:
let Time := {i in TotalDays: ord(i)<=period};
set Weekends = {i in Time: WhichWeekDay[i] in {6,7}};

#We define our holidays, days when we do not produce, as the sum  of the weekends and the festivities:
let Holidays:= Festivities union Weekends;

#We specify the days of the week when we can deliver:
let DeliveryDays := {i in ProductionDays: WhichWeekDay[i] in DeliveryDaysWeek};

#In our model, the work time per day will be the same for every day and it will be measured in minutes:
let {t in ProductionDays} WorkTimeDay[t] := 60*WorkHoursDay;

#In our model, we number carts from 1 to NumCarts and all of them have the same capacity:
let Carts:= 1..NumCarts;
let {c in Carts} StorageCapacity[c] := CartsCapacity;





