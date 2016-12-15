'''
map_search_api:
    dependency module that provide access to
    a global overview of map and service:
'''

''' [function] bpm_situation_snapshot() '''
# returns the latest overview of:
#  Cars: location, battery_charge, is_charging
#   [!] only available cars are listed
#  FieldStaff: location, list of pending_requests
#       Request: target_car, destination
#  CityZone:
#   safe_areas list, powerplug_slots list, number_of_parked_cars,
#   optimal_number_of_cars
#  SafeAreas: boundaries, capacity, parked_cars list, number_of_parked_cars,
#   city_zone
#  PowerPlugSlots: location, parked_car, boudaries, city_zone

''' [function] park_search(location, radius): '''
# returns the list of safe areas or power plug slots
# within a certain <radius> from <location>

''' [function] estimate_battery_consumption(current_location,destination,time) '''
# Returns the estimated battery consumption if a car travels
# from <current_location> to <destination>.
# The prediction is computed by an artificial neural network,
# trained with data extracted from cars' log

from map_search_api import bpm_situation_snapshot, park_search,
                            estimate_battery_consumption
