open util/time

--Signatures
sig Username {}
sig Password {}
sig FiscalCode{}
sig IDNumber{}
sig LicensePlate{}
sig StreetName{}

sig GPSPosition{--coordinates are scaled to simplify the problem
	x: one Int,
	y: one Int
}{(x <= 3 and x>=-3) and (y>=-6 and y<=6)}

sig Registration{
	username: one Username,
	psw: one Password
}

abstract sig Customer{
	registration : one Registration
}
sig EndUser extends Customer{
	fc: one FiscalCode,
	reports: set TrafficViolationReport
}
sig Authority extends Customer{
	idNumber: one IDNumber,
	checkedReports: set TrafficViolationReport
}
sig Vehicle {
	plate: one LicensePlate,
	reports: set TrafficViolationReport
}
sig Street{
	name: one StreetName,
	coordinates: set GPSPosition,
	reports: set TrafficViolationReport
}
sig TrafficViolationReport{
	id : one Int,
	vehicle: one Vehicle,
	pos: one GPSPosition,
	reporter: one EndUser,
	status: ReportStatus one-> Time
}{id>0}

abstract sig ReportStatus{}
sig Confirmed extends ReportStatus{}
sig Rejected extends ReportStatus{}
sig Unchecked extends ReportStatus{}

--Facts

--Every customer has a unique username
fact uniqueUsernames{
	no disj c1, c2: Customer | c1.registration.username=c2.registration.username
}

--Every End User has a unique FiscalCode
fact uniqueFiscalCode{
	no disj eu1,eu2: EndUser |eu1.fc=eu2.fc
}
--Every Authority has a unique ID Number
fact uniqueIDNumber{
	no disj a1,a2: Authority|a1.idNumber=a2.idNumber
}
--Every vehicle has a unique license plate
fact uniqueLicensePlates{
	no disj v1, v2: Vehicle | v1.plate=v2.plate
}
--Every TrafficViolationReport has a unique ID number
fact uniqueNumber{
	no disj tvr1, tvr2: TrafficViolationReport | tvr1.id=tvr2.id
}

--The Status of a traffic violation report is firstly Unchecked,
--then (after the checking process) it becomes Confirmed or Rejected
fact staticReportStatus{
	all tvr: TrafficViolationReport| one t':Time|tvr.status.t' = Unchecked
	all tvr: TrafficViolationReport, t: Time|
		 (tvr.status.t = Confirmed  =>	all t': Time| gte[t',t] => tvr.status.t' = Confirmed)
	and 
		(tvr.status.t = Rejected  =>all t': Time| gte[t',t] => tvr.status.t' = Rejected)
}
--all vehicles have the traffic violation reports which involve it in the set of reports
fact vehicleReports{
	all v: Vehicle, tvr :TrafficViolationReport| (tvr.vehicle =v <=> tvr in v.reports)
}

--all reporter have in their set of traffic violations, the traffic violation made by themselves
fact vehicleReports{
	all eu: EndUser, tvr :TrafficViolationReport| (tvr.reporter =eu <=> tvr in eu.reports)
}

--streets have a disjointed set of GPSPositions 
fact disjStreets{
	some  gps1: GPSPosition| no disj s1, s2: Street|gps1 in s1.coordinates and gps1 in s2.coordinates
}

--all GPSPosition in a street
fact gpsPositionInAStreet{
	all gps: GPSPosition, s: Street| gps in s.coordinates
}

--if GPS coordinates are the position of a report and are part of a street, that street has the report in her set of reports
fact streetCoherence{
	all s: Street, gps: GPSPosition, tvr: TrafficViolationReport| (gps = tvr.pos and gps in s.coordinates) <=> tvr in s.reports
}

--each report is checked by one and only one authority
fact noDifferentAuthoritiesCheckTheSameReport{
	no disj a1, a2: Authority, tvr:TrafficViolationReport| (tvr in a1.checkedReports) and (tvr in a2.checkedReports)
}


pred world1{
	some tvr: TrafficViolationReport, t: Time| tvr.status.t=Rejected
}
run world1 for 1 but exactly 2 Time, exactly 2 Username, exactly 2 Password, exactly 2 Registration, exactly 2 LicensePlate, exactly 2 Vehicle, exactly 2 GPSPosition, exactly 2 Customer, exactly 1 IDNumber, exactly 1 FiscalCode ,exactly 2 ReportStatus, exactly 2 TrafficViolationReport
--run world1 for 1 but exactly 2 Username, exactly 2 Password, exactly 2 Registration, exactly 2 Customer, exactly 1 FiscalCode, exactly 1 IDNumber, exactly 1 Street, exactly 1 Vehicle, exactly 1 LicensePlate,
	--exactly 1 TrafficViolationReport, exactly 1 GPSPosition
