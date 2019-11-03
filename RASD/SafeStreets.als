sig Username {}
sig Password {}
sig FiscalCode{}

sig GPSPosition{
	x: one Int,
	y: one Int
}{(x <= 90 and x>=-90) and (y>=-180 and y<=180)}

sig Registration{
	username: one Username,
	psw: one Password
}

abstract sig Customer{
	registration : one Registration
}

sig EndUser extends Customer{
	fc: one FiscalCode,
	pos: one GPSPosition,
	reports: set TrafficViolationReport
}


sig Authority extends Customer{
	idNumber : one IDNumber,
	confirmedReports: set TrafficViolationReport
	rejectedReports: set TrafficViolationReport
}

sig Vehicle {
	plate: one String,
	reports: set TrafficViolationReport
}

sig Street{
	name: String,
	reports: set TrafficViolationReport 
}

abstract sig ReportStatus{}
sig Confirmed extends ReportStatus{}
sig Rejected extends ReportStatus{}
sig Unchecked extends ReportStatus{}

sig TrafficViolationReport{
	id : one String,
	vehicle: one Vehicle,
	pos: one GPSPosition,
	reporter: one EndUser,
	status: one ReportStatus
}

--Every customer has a unique username
fact uniqueUsernames{
	no disj c1, c2: Customer | c1.registration.username=c2.registration.username
}

--Every vehicle has a unique license plate
fact uniqueLicensePlates{
	no disj v1, v2: Vehicle | v1.plate=v2.plate
}


















