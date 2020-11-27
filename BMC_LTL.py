def BMC_LTL(n,threshold,init,trans,ast):
  s_i = [Bool('s_0_%d'%(i)) for i in range(n)]
  s=Solver()
  s.add(init(s_i[0]))
  mem={}
  no_loop = Not(False)
  for k in range(threshold):
    s.add(nonLooping(ast,0,k,s,mem))
    s.push()
    no_Loop = And(no_Loop,s_i[k]==s_i[k+1])
    s.add(no_Loop)
    s.add('nl_%s_%d_0',(ast.vp,k))
    if s.check() == sat:
      return trace_print(n,k,ast)
    s.pop()
    for l in range(k):
      s.add(ltl_looping_encode(0,l,k,ast,s,mem))
      s.push()
      s.add(Trans(s_i[k],s_i[l]))
      s.add('lp_%s_%d_0_%d',(ast.vp,k,l))
      if s.check() == sat:
        return trace_print(n,k,ast)
      s.pop()
      s.add(Trans(s_i[k],s_i[k+1]))
