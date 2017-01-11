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
