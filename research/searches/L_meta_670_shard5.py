"""Exact bounded circuit synthesis for desk shard L-meta-670/5.

The first paid gate is AND(x_0,x_4). Every later gate is AND/OR of
at most two inputs or NOT. Unary copies use duplicated operands; empty
AND uses mode 3 (true); empty OR and missing-wire reads use a false
source. NOT reads only its first input. This matches Circuit.eval.

A circuit with fewer than the budget gates can be padded with copies.
Its designated output can be moved to the end of its live subgraph and
then copied. The prescribed first gate stays first, even if unused.
Thus a fixed-budget, final-output encoding covers every smaller circuit
in this shard. The target is not an input or a constant.

CEGIS constrains selected assignments, then independently evaluates every
candidate on all 2^n inputs. UNSAT on a subset entails no full witness.
Timeout and interruption are never reported as exhaustion.
"""
import argparse,datetime,hashlib,itertools,json,os,threading,time,urllib.request,urllib.error
from pathlib import Path
from z3 import SolverFor,BitVec,BitVecVal,Bool,BoolVal,If,And,Or,Not,ULT,ULE,sat,unsat

EDGES=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]

def now(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def table(n,fn): return sum(1<<x for x in range(1<<n) if fn(x))

class Search:
    def __init__(self,n,budget,first,target):
        self.n=n;self.budget=budget;self.first=first;self.target=target
        self.bits=max(1,(n+budget+1).bit_length())
        self.solver=SolverFor('QF_BV');self.samples=set()
        self.ops=[];self.aa=[];self.bb=[]
        for k in range(budget):
            op=BitVec('op_%d'%k,2);a=BitVec('a_%d'%k,self.bits);b=BitVec('b_%d'%k,self.bits)
            limit=n+1+k
            self.solver.add(ULT(a,limit),ULT(b,limit))
            self.solver.add(Or(op==2,op==3,ULE(a,b)))
            self.solver.add(Or(op!=2,b==a))
            self.solver.add(Or(op!=3,And(a==0,b==0)))
            self.ops.append(op);self.aa.append(a);self.bb.append(b)
        self.solver.add(self.ops[0]==0,self.aa[0]==first[0],self.bb[0]==first[1])

    def add(self,x):
        if x in self.samples:return
        self.samples.add(x)
        values=[BoolVal(bool(x>>i&1)) for i in range(self.n)]+[BoolVal(False)]
        def select(index):
            result=values[-1]
            for i in reversed(range(len(values)-1)):
                result=If(index==i,values[i],result)
            return result
        for k in range(self.budget):
            av=select(self.aa[k]);bv=select(self.bb[k]);v=Bool('v_%d_%d'%(x,k))
            self.solver.add(v==If(self.ops[k]==0,And(av,bv),
                If(self.ops[k]==1,Or(av,bv),If(self.ops[k]==2,Not(av),BoolVal(True)))))
            values.append(v)
        self.solver.add(values[-1]==BoolVal(bool(self.target>>x&1)))

    def candidate(self,model):
        return [(model.eval(o).as_long(),model.eval(a).as_long(),model.eval(b).as_long())
                for o,a,b in zip(self.ops,self.aa,self.bb)]

    def evaluate(self,candidate):
        width=1<<self.n;mask=(1<<width)-1
        values=[table(self.n,lambda x,i=i:x>>i&1) for i in range(self.n)]+[0]
        for op,a,b in candidate:
            assert 0<=a<len(values) and 0<=b<len(values)
            av,bv=values[a],values[b]
            values.append((av&bv) if op==0 else ((av|bv) if op==1 else ((mask^av) if op==2 else mask)))
        assert candidate[0]==(0,*self.first)
        return values[-1]

    def lean_circuit(self,candidate):
        def wire(i): return i if i<self.n else (self.n+self.budget if i==self.n else i-1)
        return [{'op':['and','or','not','and'][op],
                 'inputs':[] if op==3 else ([wire(a)] if op==2 else [wire(a),wire(b)])}
                for op,a,b in candidate]

def selftest():
    # Exhaustively compare all two-variable truth tables with a separate
    # enumeration of every possible second gate, including constants.
    n=2;first=(0,1);mask=15
    inputs=[table(n,lambda x,i=i:x>>i&1) for i in range(n)]
    base=inputs+[0,inputs[0]&inputs[1]]
    reachable={mask}
    for a in base:
        reachable.add(mask^a)
        for b in base:reachable.update([a&b,a|b])
    for target in range(16):
        search=Search(n,2,first,target)
        for x in range(4):search.add(x)
        result=search.solver.check()
        assert (result==sat)==(target in reachable),(target,result,reachable)
        if result==sat:
            c=search.candidate(search.solver.model())
            assert search.evaluate(c)==target
            gates=search.lean_circuit(c)
            # A second evaluator uses actual Lean wire indices and missing reads.
            for x in range(4):
                wires=[bool(x>>i&1) for i in range(n)]
                for g in gates:
                    vs=[wires[i] if i<len(wires) else False for i in g['inputs']]
                    wires.append(all(vs) if g['op']=='and' else (any(vs) if g['op']=='or' else not(vs[0] if vs else False)))
                assert wires[-1]==bool(target>>x&1)
    print('Self-test passed: all 16 truth tables, exhaustive two-gate comparison.',flush=True)


def run(seconds,lease):
    n=9;budget=15;target=table(n,lambda x:any(x>>a&1 and x>>b&1 for a,b in EDGES))
    search=Search(n,budget,(0,4),target)
    root=Path(__file__).resolve().parent
    statepath=root/'petersen-shard5-status.json'
    digest=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    state={'status':'running','started_utc':now(),'pid':os.getpid(),'gap':'L-meta-670',
           'shard':5,'first_gate':'AND(x_0,x_4)','gate_budget':15,'time_limit_seconds':seconds,
           'program_sha256':digest,'rounds':0,'samples':0,'lease':lease,
           'note':'Solver search, not a Lean proof or an accepted PR.'}
    lock=threading.Lock();stopped=threading.Event();withdrawn=threading.Event()
    def save():
        with lock:
            temporary=statepath.with_suffix('.tmp')
            temporary.write_text(json.dumps(state,indent=2)+'\n');temporary.replace(statepath)
    def post(path):
        with urllib.request.urlopen(urllib.request.Request('https://pequalnp.com/desk/'+path,method='POST'),timeout=20) as r:
            return json.loads(r.read())
    def beat():
        while not stopped.wait(540):
            try:
                response=post('beat?lease='+lease)
                state['last_renewal_utc']=now();state['renewal_response']=response;save()
            except urllib.error.HTTPError as e:
                state['renewal_error']=str(e);save()
                if e.code==410:
                    withdrawn.set();search.solver.interrupt();return
            except Exception as e:
                state['renewal_error']=repr(e);save()
    save()
    if lease:threading.Thread(target=beat,daemon=True).start()
    for x in range(1<<n):
        value=bool(target>>x&1)
        minimal=value and all(not(target>>(x^(1<<i))&1) for i in range(n) if x>>i&1)
        maximal=not value and all(target>>(x|(1<<i))&1 for i in range(n) if not(x>>i&1))
        if minimal or maximal or x.bit_count()<=1 or x==(1<<n)-1:search.add(x)
    deadline=time.monotonic()+seconds
    try:
        while True:
            remaining=deadline-time.monotonic()
            if withdrawn.is_set():state['status']='withdrawn';break
            if remaining<=0:state['status']='timeout';break
            search.solver.set(timeout=max(1,int(remaining*1000)))
            state['rounds']+=1;state['samples']=len(search.samples);state['last_check_started_utc']=now();save()
            result=search.solver.check()
            print(json.dumps({'round':state['rounds'],'samples':len(search.samples),'result':str(result),'utc':now()}),flush=True)
            if withdrawn.is_set():state['status']='withdrawn';break
            if result==unsat:
                state['status']='exhausted';state['solver_result']='unsat'
                (root/'petersen-shard5-unsat.smt2').write_text(search.solver.to_smt2())
                save()
                if lease:
                    state['desk_report']=post('release?lease='+lease+'&reason=exhausted&program='+digest)
                break
            if result!=sat:
                state['status']='unknown';state['reason']=search.solver.reason_unknown();break
            candidate=search.candidate(search.solver.model())
            difference=search.evaluate(candidate)^target
            if difference==0:
                state['status']='witness_found';state['gates']=search.lean_circuit(candidate)
                state['output_wire']=n+budget-1;state['verified_all_inputs']=1<<n
                break
            errors=[x for x in range(1<<n) if difference>>x&1]
            state['last_candidate_errors']=len(errors)
            # Add up to 24 assignments spread across the erroneous truth table.
            additions=errors if len(errors)<=24 else [errors[i*len(errors)//24] for i in range(24)]
            for x in additions:search.add(x)
            save()
    except Exception as e:
        state['status']='failed';state['error']=repr(e)
    finally:
        stopped.set();state['finished_utc']=now();state['samples']=len(search.samples);save()
        print(json.dumps(state),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--self-test',action='store_true');p.add_argument('--seconds',type=int,default=1800);p.add_argument('--lease')
    args=p.parse_args()
    if args.self_test:selftest()
    else:run(args.seconds,args.lease)
