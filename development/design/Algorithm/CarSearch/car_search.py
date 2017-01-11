# dependency module that handles DBMS connection behind the scenes
# and provides tools for data managing
# TO_OBJECT_ARRAY is a constant to pass to <result_formatter(results, conversion_type)>
# <execute_query( query )> runs a query in dbms and return <results>
from dbms_api import execute_query, result_formatter, TO_OBJECT_ARRAY
DEFAULT_RADIUS = 500 # meters (CONSTANT)

def search_car(location, radius=DEFAULT_RADIUS):
    '''
        Compute the set of available cars within <radius> from <location>.
        Params:
            <location>: a GPS coordinate (latitude,longitude)
            <radius>: the search radius (in meters),
                        defaults to DEFAULT_RADIUS if not setted
        returns:
            an array of object with fields {lat,lon,battery_aut},
            corresponding to searched cars
    '''
    (lat, lon) = position # get latitude and longitude from location
    # query a SQL (2008+) DBMS for available cars.
    # <location> field of <cars> table is of <geography> SQL type,
    #   has .Lat and .Long attributes
    #   can compute accurate distance from other <geography> variables
    #       through <.STDistance(other_location)> method
    available_cars_query = '''
        SET @orig_lat={orig_lat}
        SET @orig_lon={orig_lon}
        DECLARE @orig geography = geography::Point(@orig_lat, @orig_lng, 4326);
        DECLARE @radius int
        SET @radius={radius}
        SELECT location.Lat AS lat, location.Long AS lon,
                battery_autonomy AS battery_aut
            FROM cars
            WHERE availability = 'available' AND @orig.STDistance(location) < @radius;
    '''.format(orig_lat=lat, orig_lon=lon,radius=radius) # set parameters in query
    results = execute_query( available_cars_query )
    return result_formatter( results, TO_OBJECT_ARRAY )
