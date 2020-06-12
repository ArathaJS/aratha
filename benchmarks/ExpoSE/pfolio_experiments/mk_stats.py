import csv

SOLVERS = ('G-Strings', 'cvc4', 'z3', 'pfolio_simple', 'pfolio_nogood')
N_PROBS = 197
TIMEOUT = 300
COVMODE = 'stmt'

results = {}
coves = dict((s, 0.0) for s in SOLVERS)
nimps = dict((s, 0.0) for s in SOLVERS)
times = dict((s, 0.0) for s in SOLVERS)
touts = dict((s, 0) for s in SOLVERS)
infile = 'results-total.log'
reader = csv.reader(open(infile), delimiter = '|')
n = 0

for row in reader:
#  print row
  n += 1
  solv = row[0]  
  inst = row[1][row[1].rfind('/')+1:]
#  if inst in BLACK_LIST:
#    continue
  code = int(row[2])
  try:
    if (COVMODE == 'stmt'):
      cove = round(float(row[3]), 2)
    elif (COVMODE == 'branch'):
      cove = round(float(row[4]), 2)
    elif (COVMODE == 'func'):
      cove = round(float(row[5]), 2)
    elif (COVMODE == 'line'):
      cove = round(float(row[6]), 2)
  except ValueError:
    cove = 0
  if (cove == 0):
    print "Warning! 0% coverage for",inst,"with solver",solv
  nimp = int(row[7])
  if float(row[8]) >= TIMEOUT:
    time = TIMEOUT
    touts[solv] += 1
    if solv.startswith('pfolio'):
      print row
  else:
    time = float(row[8])
  if not inst in results.keys():
    results[inst] = {}
  results[inst][solv] = (cove, time, round(float(row[3]), 2) if COVMODE == 'line' else round(float(row[6]), 2))
  coves[solv] += cove
  nimps[solv] += nimp
  times[solv] += time

#assert n == len(SOLVERS) * N_PROBS
n = N_PROBS
print 'Total # problems',n
print 'Average %',COVMODE,'coverage:', sorted(((s, round(coves[s]/n,2)) for s in SOLVERS), key = lambda x: -x[1])
print 'Average # unique inputs:', sorted(((s, round(nimps[s]/n,2)) for s in SOLVERS), key = lambda x: -x[1])
print 'Average time [sec.]:', sorted(((s, round(times[s]/n,2)) for s in SOLVERS), key = lambda x:  x[1])
print 'Number of timeouts:', sorted(((s, round(touts[s],2)) for s in SOLVERS), key = lambda x:  x[1])
print '=========='

vbs_time = 0.0
vbs_stmt = 0.0
vbs_line = 0.0
better = dict(((s_i, s_j), 0) for s_i in SOLVERS for s_j in SOLVERS if s_i != s_j)
for inst, item in results.items():
#  print inst, item
  m = max([(item[s][0], -item[s][1], item[s][2]) for s in ('G-Strings', 'cvc4', 'z3')])
  vbs_time += -m[1]
  if COVMODE == 'stmt':
    vbs_stmt += m[0]
    vbs_line += m[2]
  else:
    vbs_stmt += m[2]
    vbs_line += m[0]
  for i in range(0, len(SOLVERS)):
    s_i = SOLVERS[i]    
    cov_i = item[s_i][0]
    for j in range(i + 1, len(SOLVERS)):
      s_j = SOLVERS[j]
      cov_j = item[s_j][0]
      if (cov_i > cov_j):
        better[(s_i, s_j)] += 1
        if s_j.startswith('pfolio') and i == 0:
          print 'ooops',inst, item
      elif (cov_i < cov_j):
        better[(s_j, s_i)] += 1
        if s_j.startswith('pfolio') and i == 0:
          x = [k for k in range(0, j - 1) if k != j and cov_j > item[SOLVERS[k]][0]]
          if len(x) == len(SOLVERS) - 2:
             print inst, item, x
              
for s, n in sorted(better.items()):
  print s[0],'has better',COVMODE,'coverage than',s[1],':',n,'times'
print '=========='

faster = dict(((s_i, s_j), 0) for s_i in SOLVERS for s_j in SOLVERS if s_i != s_j)
for inst, item in results.items():
#  print inst, item
  for i in range(0, len(SOLVERS)):
    s_i = SOLVERS[i]
    cov_i = item[s_i][0]
    time_i = item[s_i][1]
    for j in range(i + 1, len(SOLVERS)):
      s_j = SOLVERS[j]
      cov_j = item[s_j][0]
      time_j = item[s_j][1]
      if (cov_i >= cov_j and time_i < time_j):
        faster[(s_i, s_j)] += 1
      elif (cov_i <= cov_j and time_i > time_j):
        faster[(s_j, s_i)] += 1
for s, n in sorted(faster.items()):
  print s[0],'is faster than',s[1],'when',COVMODE,'coverage is better or equal:',n,'times'
print '=========='

print('VBS_' + COVMODE + ' line coverage ):', vbs_line/N_PROBS)
print('VBS_' + COVMODE + ' stmt coverage ):', vbs_stmt/N_PROBS)
print('VBS_' + COVMODE + ' time):', vbs_time/N_PROBS)





