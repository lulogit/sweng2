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
# [!]: higher priority values means less priority,
#       cars will be sorted by <relocation_priority> in DESCENDANT ORDER
# e.g: -2 is the lowest possible value,
#       thus a car with priority -2 will be the first to be relocated

# recommend destination only within this radius from user's destination
MONEY_SAVING_RADIUS = 1000 # meters
MAX_MONEY_SAVING_DISCOUNT = 0.10 # 10%
