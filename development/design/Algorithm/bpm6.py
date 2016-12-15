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
