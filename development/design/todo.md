# final check

# git repository:
- upload production and release
- prepare for presentation
- commit

## rasd:
- eliminare "locate facilities" da requisiti
- eliminate R.20
- bpm -> generl purpose reqs.

### changes:
- specify car system interface
- separation of concerns in modules
- grasp future evolution of components
- too high level of abstraction (in end), then BCE diagram (wtf?!?!?)
- no BCE in architecture
- highlight and clarify the connection on all the components in your presentation
  (in terms of naming connections, warnings)
- final presentation: provide overview / wait for question
- TIME, TIME, TIME !!! (giga penalization)
- data flow, not UX diagram
- correct car_search.py

### design choices (check):
- java EE (server stack):
  * entity beans [+]
  * pooling
  * persistency [+]
- DBMS choice, microsoft SQL:
  * performances
  * plugin <geography> [+]
  * db as "blackboard"
- front end:
  * JS + html5 + CSS stack --> webapp
  * plenty of developers --> cheaper [+]
  * portability [+]
  * flexibility [+]
  * PhoneGap to embed into native app --> no loose marketplaces [+]
- number of parallel server:
  * computed to guarantee availability and reliability
- load balancer:
  * performance, reliability
- db backupper:
  * availability, data protection
- 4 tier:
  * security
  * secrecy of code
  * different components
  * all logic internal
  * http logic extern
  * java EE compliant
