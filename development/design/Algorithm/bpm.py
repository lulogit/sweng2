
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

''' [function] distance_autonomy(car) '''
# returns the car autonomy in meters ()
from car import distance_autonomy

''' [function] get_discounts(car, battery_consumption, destination) '''
# return the total applicable discount amount (percentage)
#   if <car> travel to <destination> (a safe area or a power plug slot)
#   <battery_consumption> is taken into account
#   number of passenger is not taken into account
from service_configuration.discounts import compute_discount


''' [function] assign_relocation(field_staff_member, task, [priority]) '''
# add <task> (relocation) to <field_staff_member>'s task queue,
# considering an optional <priority>

''' [function] field_staff_list() '''
# return a list of active field staff users, with their task queues
from field_staff_manager import assign_relocation, field_staff_list

# threshold values for car's battery charge percentage
EMPTY_BATTERY = 0.05 # 5%
FULL_BATTERY = 0.95 # 98%

# weight for criteria used in computation of car's relocation priority
IMPORTANCE_HIGH = 1e10 # weight used for city zone criterion
IMPORTANCE_LOW = 1e5 # weight used for safe area criterion

# some conventional values for car's relocation priority
PRIORITY_HIGH = -1 # high priority to relocate a car with empty battery
                   # in a power plug slot
PRIORITY_HIGHEST = -2 # maximum priority to relocate an already-charged car
                      # away from a power plug slot

# recommend destination only within this radius from user's destination
MONEY_SAVING_RADIUS = 1000 # meters
MAX_MONEY_SAVING_DISCOUNT = 0.10 # 10%

def compute_cars_relocation_priority(map_state):
    '''
        A priority to relocate a car away from a parking solution
        is computed according to:
            1) the car is charged, but still in powerplug slot
            2) the car has empty battery, but not in powerplug slot
            3) city_zone overpresence of cars
            4) safe area load factor (higher priority to full safe areas)
        Higher priority correspond to lower relocation_priority values.
    '''
    updated_state = map_state
    for zone in updated_state.city_zones:
        zone.car_delta = zone.number_of_parked_cars-zone.optimal_number_of_cars
        if zone.car_delta > 0:
            zone_priority = 1 / zone.car_delta * IMPORTANCE_HIGH
        else:
            zone_priority = IMPORTANCE_HIGH
        for area in zone.safe_areas:
            load_factor = area.number_of_parked_cars / area.capacity
            area_priority = zone_priority + load_factor * IMPORTANCE_LOW
            for car in safe_areas.parked_cars:
                if car.battery_charge > FULL_BATTERY and car.is_charging:
                    car.relocation_priority = PRIORITY_HIGHEST
                elif car.battery_charge < EMPTY_BATTERY and not car.is_charging:
                    car.relocation_priority = PRIORITY_HIGH
                else:
                    car.relocation_priority = area_priority
    return updated_state
def compute_safe_areas_relocation_priority(map_state):
    '''
        A priority to relocate a car into a parking solution
        is computed according to:
            1) city_zone underpresence of cars
            2) safe area load factor (higher priority to empty safe areas)
        Higher priority correspond to lower relocation_priority values.
    '''
    updated_state = map_state
    for zone in updated_state.city_zones:
        zone.car_delta = zone.number_of_parked_cars-zone.optimal_number_of_cars
        if zone.car_delta < 0:
            zone_priority = -1 / zone.car_delta * IMPORTANCE_HIGH
        else:
            zone_priority = IMPORTANCE_HIGH
        for area in zone.safe_areas:
            load_factor = area.number_of_parked_cars / area.capacity
            area.relocation_priority =
                zone_priority + (1-load_factor)*IMPORTANCE_LOW
        for plugslot in zone.powerplug_slots:
            plugslot.relocation_priority = 1 * IMPORTANCE_LOW
    return updated_state
def compute_field_staff_relocations(map_state, field_staff_users):
    '''
        Assign to each field staff user a maximum of 2 relocation tasks.
        The tasks consist in relocating a car to another parking solution
        (safe area / powerplug slot) and are chosen by relocation_priority
        of cars in <map_state>.
        Takes as input the list of <field_staff_users>.
        Charge-related car relocations have priority,
        field staff users with more than 2 task in queue
        are not taken into account for other kind of relocation.

        Returns a list of Relocation:
            Relocation.field_staff_member : selected field staff user,
            Relocation.task : the actual task to perform's informations
    '''
    assignable_users = sort(
        field_staff_users as user,
        by=user.queue_length,
        ASCENDING )
    cars = sort(
        map_state.get_cars() as car,
        by=car.relocation_priority,
        ASCENDING )
    safe_areas = sort(
        map_state.get_safe_areas() as area,
        by=area.relocation_priority,
        ASCENDING )
    powerplug_slots = filter(
        map_state.get_power_plug_slots() as slot,
        where =  slot.is_free() )
    relocation_requests = []
    for car in cars:
        assigned_user = assignable_users.pop()
        if car.relocation_priority == PRIORITY_HIGHEST:
            # remove charged car from powerplug slot
            assigned_destination = safe_areas.pop()
        elif car.relocation_priority == PRIORITY_HIGH:
            # relocate empty-battery car to powerplug slot
            assigned_destination = powerplug_slots.pop()
        else:
            if assigned_user.queue_length < 2:
                assigned_destination = safe_areas.pop() OR powerplug_slots.pop()
            else:
                exit_loop()
        if assigned_destination:
            relocation_requests.append( {
                field_staff_member : assigned_user,
                task: {
                    car: car,
                    destination: assigned_destination
                }
            } )
            # add user to queue, since has less than 2 tasks
            if assigned_user.queue_length+1 < 2:
                assignable_users.add_last(assigned_user)
    return (updated_state,relocation_requests)
def compute_discounts_for_safe_areas(map_state):
    '''
        Compute an additional discount (up to MAX_MONEY_SAVING_DISCOUNT),
        if user park in that specific parking solution
        during a money saving rent.

        The discount is proportional to
        the relocation_priority of that safe area.
    '''
    updated_state = map_state
    for zone in updated_state.city_zones:
        for area in zone.safe_areas:
            area.money_saving_discount =
                ((IMPORTANCE_HIGH - area.relocation_priority) / IMPORTANCE_HIGH)
                * MAX_MONEY_SAVING_DISCOUNT
        for plugslot in zone.powerplug_slots:
            # power plug slots already receive discount
            plugslot.money_saving_discount = 0
    return updated_state
# MAIN ALGORITHM FUNCTIONALITIES
def bpm_cycle():
    '''
        Main cycle of BPM algorithm:
            - assign relocations to field staff users
            - pre compute money saving discounts for parking solutions

        Repeated every 15 minutes.
    '''
    map_state = bpm_situation_snapshot()
    map_state = compute_cars_relocation_priority(map_state)
    map_state = compute_safe_areas_relocation_priority(map_state)
    field_staff_users = field_staff_list()
    (map_state, relocations) = compute_field_staff_relocations(
        map_state,
        field_staff_users)
    map_state = compute_discounts_for_safe_areas(map_state)
    # STORE map_state FOR NEXT 15 minutes
    for relocation in relocations: # assign relocations to field staff
        assign_relocation(relocation.assigned_staff_member, relocation.task)
def money_saving_reccomend(map_state, destination, car):
    '''
        Recommend an alternative destination for the user,
        to guarantee the maximum possible discount to an user driving <car>,
        willing to go to <destination>.

        An additional money_saving_discount
        is considered for each parking solution.
    '''
    recommended_destination = find(
        # safe area or power plug slot
        park in park_search(destination, MONEY_SAVING_RADIUS),
        maximizing:
            compute_discount(
                car,
                estimate_battery_consumption(car.location, park, time.now()),
                park
            ) + map_state.get(park).money_saving_discount
            # get discount previously computed for that safe area
    )
    return recommended_destination
