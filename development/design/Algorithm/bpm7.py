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
