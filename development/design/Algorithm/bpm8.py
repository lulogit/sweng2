# MAIN ALGORITHM FUNCTIONALITIES
def bpm_cycle():
    '''
        Main cycle of BPM algorithm:
            - assign relocations to field staff users
            - pre compute money saving discounts for parking solutions

        Repeated every 25 minutes.
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
