# This file contains the model for Phase 2 of IEMS 313 SmartRail project.
#
# Author: Jason Lu, Rhea Shah, Hugo Zhang, Gabe Bider
# Date: May 29, 2023

# ================
#      SETS
# ================

# The set of stations. 
set stations;

# The set of tracks (directed). 
set tracks within (stations cross stations); 

# The set of shipments. 
set shipments; 

# The set of biweekly days.
set days;

# The reverse set of tracks (Used to create bi-directional tracks in AMPL)
set tracks_reverse within (stations cross stations);

# ================
#    Parameters
# ================

# The length of each track (in miles). 
param x_coord {stations};
param y_coord {stations};
param len_track{(i,j) in tracks} := sqrt((x_coord[i]-x_coord[j])^2 + (y_coord[i]-y_coord[j])^2);

# The number of reloading zones at each station.
param num_reload {stations}; 

# The reloading cost per container. 
param cost_reload;

# The shipping cost per container per mile. 
param cost_ship;

# Capacity per train/track in a day. 
param capa_track; 

# Capacity per reloading zone in a day. 
param capa_reload; 

# Number of days in the biweekly schedule
param T;

# Daily late penalty fee per shipment
param cost_penalty;

# Daily amortized cost for building a new track
param cost_track;

# Daily amortized cost for building a new reloading station
param cost_new_reload;

# Max number of reload stations per station
param max_reload;

# Max number of tracks between two stations
param max_tracks;

# The origins, destinations, and volumes of the shipments.
param orig {shipments} within stations;
param dest {shipments} within stations;
param volume {shipments};

# Days when shipments become available for pickup and should be delivered
param avail_day {shipments};
param deliv_day {shipments};


# ================
#    Variables
# ================

# The number of containers traversed along track from station i
# to station j belonging to shipment k on day d. 
var N{tracks, shipments, days} integer >= 0;

# The number of new tracks between station i and station j
var new_tracks{tracks} integer >= 0;

# The number of new reloading zones constructed at station i
var new_reload_zones{stations} integer >= 0;

# The number of containers picked up from station i for shipment k on day d
var pickup{stations, shipments, days} integer >= 0;

# The number of containers delivered to station i for shipment k on day d
var deliver{stations, shipments, days} integer >= 0;

# Binary variable keeping track if d is less than or equal to deliv_day for shipment k
var late{shipments, days} binary >= 0;


# Used for checking the objective value. 
var total_ship_cost = sum {(i,j) in tracks, k in shipments, d in days} cost_ship * len_track[i,j] * N[i,j,k,d];
var new_tracks_cost = sum {(i,j) in tracks_reverse, d in 1..T} cost_track * new_tracks[i,j] * len_track[i,j]; 
var new_reloads_cost = sum {i in stations, d in days} cost_new_reload * new_reload_zones[i]; 
var total_late_cost = sum {(i,j) in tracks, k in shipments, d in days} cost_penalty * N[i,j,k,d] * late[k,d];

# ================
#    Obj. Func
# ================

# We aim to minimize the total cost, including the shipping cost, amortized tracks cost, 
# new reloading station cost, and late penalty cost.
 
minimize total_cost:
    total_ship_cost + new_tracks_cost + new_reloads_cost + total_late_cost;
    
# ================
#   Constraints
# ================


# new_tracks[i,j] should be equal to new_tracks[j,i] for all i,j
subject to track_equality {(i,j) in tracks}:
    new_tracks[i,j] = new_tracks[j,i];

# The max number of tracks existing between two stations is at most max_tracks
subject to track_limit {(i,j) in tracks}:
    new_tracks[i,j] + 1 <= max_tracks;
   
# The max number of reloading stations existing at a station is at most max_reload
subject to reload_station_limit {i in stations}:
    new_reload_zones[i] + num_reload[i] <= max_reload; 
    
# The number of containers traversed along every track in either direction per day
# should not exceed the track capacity. 
subject to track_capa_limit {(i,j) in tracks, d in days}:
 	  sum{k in shipments} (N[i,j,k,d] + N[j,i,k,d]) <= capa_track * (new_tracks[i,j] + 1);
    
# The number of containers entering a station per day
# should not exceed the reloading zones capacity. 
subject to reload_capa_limit {j in stations, d in days}:
    sum{(i,j) in tracks, k in shipments} N[i,j,k,d] <= capa_reload * (new_reload_zones[j] + num_reload[j]);
    
# No containers should be shipped before the availability day
subject to availability_constraint {k in shipments}:
	sum{(i,j) in tracks, d in days : d < avail_day[k]}  N[i,j,k,d] = 0; 

# The containers picked up for each shipment must equal the total volume 
subject to required_pickup {k in shipments, j in stations}:
	sum{d in avail_day[k]..T-1} pickup[j,k,d] = if orig[k] == j then volume[k] else 0; 
	
# The containers delivered for each shipment must equal the total volume
subject to required_delivery {k in shipments, j in stations}:
	sum{d in avail_day[k]..T-1} deliver[j,k,d] = if dest[k] == j then volume[k] else 0;

# The containers leaving an origin station must equal the containers picked up on that day (ensures containers start moving)
subject to containers_leave_origin {i in stations, k in shipments, d in avail_day[k]..T-1}:
    sum{(orig[k],j) in tracks} N[orig[k],j,k,d] * (if orig[k] == i then 1 else 0) = pickup[i,k,d];
 
# The containerrs arriving at a destination station must equal the containers delivered on that day (ensures containers start moving)
subject to containers_arrive_destination {i in stations, k in shipments, d in avail_day[k]..T-1}:
    sum{(j,dest[k]) in tracks} N[j,dest[k],k,d] * (if dest[k] == i then 1 else 0) = deliver[i,k,d];
	  
# Containers that are delivered past the deliv_day for a shipment are considered late
subject to deliv_late {k in shipments, d in 1..T}:
	late[k,d] = if d < deliv_day[k] then 0 
	else 1;

# The number of containers entering and leaving a station are balanced. 
subject to flow_consistency {k in shipments, g in stations, d in days: d < T}: 
    sum {(i,g) in tracks} N[i,g,k,d] + pickup[g,k,d+1] = sum {(g,j) in tracks} N[g,j,k,d+1] + deliver[g,k,d];
    

    

