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
