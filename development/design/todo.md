# final check

# git repository:
- upload production and release
- prepare for presentation
- commit

## rasd:
- eliminare "locate facilities" da requisiti
- eliminate R.20
- bpm -> generl purpose reqs.

### comment component

### final modifications
- file on email

### reference

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
