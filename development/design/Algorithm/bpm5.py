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
