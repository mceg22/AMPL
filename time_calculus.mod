
set WeekDays ordered = 1..7;
set Date = {'Day','Month','Year'};
param BegginingDate{Date} integer, >0;
param BegginingDateWeekDay in WeekDays;
param period integer, >1;					#en dias




set Years ordered =BegginingDate['Year']..(BegginingDate['Year']+(period mod 365));
set Months{i in Years} circular = if i=BegginingDate['Year'] then BegginingDate['Month']..12 else 1..12;
set OddMonths{i in Years} within Months[i] = {j in Months[i]: j in {1,3,5,7,8,10,12}};
set EvenMonths{i in Years} within Months[i] = Months[i] diff OddMonths[i] diff {2};



set Days{i in Years, j in Months[i]} ordered = if i=BegginingDate['Year'] and j =BegginingDate['Month'] then
		{if j in OddMonths[i] then BegginingDate['Day']..31
		else{if j in EvenMonths[i] then BegginingDate['Day']..30
		else{if i mod 4=0 then BegginingDate['Day']..29 else BegginingDate['Day']..28}}} else{
		if j in OddMonths[i] then 1..31
		else{if j in EvenMonths[i] then 1..30
		else{if i mod 4=0 then 1..29 else 1..28}}
		};

set TotalDays ordered = union{i in Years, j in Months[i], k in Days[i,j]} {(k & '/' & j & '/' & i)};
param WhichWeekDay{i in TotalDays}:= (ord(BegginingDateWeekDay,WeekDays) + ord(i,TotalDays)-2) mod 7+1;

#We have to add some sets ans params use later:
set Festivities;
set DeliveryDaysWeek;
param WorkHoursDay > 0;

