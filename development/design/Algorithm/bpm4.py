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
