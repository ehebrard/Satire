#! /usr/bin/env python
#
##@mainpage Satire
# @authors Emmanuel Hebrard
#
# \section intro_sec What is Satire?
# Satire is a pure python SAT Conflict Driven Clause Learning solver.
# 
# \section license_sec License:
#  Satire is a Conflict Driven Clause Learning solver
#  Copyright (C) 2014 CNRS
#
#  This program is free software; you can redistribute it and/or modify
#  it under the terms of the GNU Lesser General Public License as published by
#  the Free Software Foundation; either version 2 of the License, or
#  (at your option) any later version.
#
#  This program is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#  GNU Lesser General Public License for more details.
#  You should have received a copy of the GNU Lesser General Public License
#  along with this program; if not, write to the Free Software
#  Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
#
#  The author may not be bothered electronically or otherwise


import sys

from definitions import *
from structures import *
import statistics as stat
        
        
########################################
######## CLAUSE AND CLAUSE BASE ########
########################################
class Clause(array):
    """docstring for Clause"""
    def __new__(cls, elts):
        return array.__new__(cls, 'I', elts)
        
    def __str__(self): 
        return '('+' '.join([lit_to_str(p) for p in self])+')'
          
class ClauseBase:
    def __init__(self, num_atoms=DEFAULT_SIZE, clauses=[]):
        self._status  = array('i')
        self._clauses = []
        self._learnts = []
        self._watcher_of = [array('I') for i in range(2*num_atoms)]
        for clause in clauses:
            if len(clause)>1:
                self._unchecked_add_(clause)
        
    def resize(self, n):
        for i in range(len(self._watcher_of), n):
            self._watcher_of.append([])
        
    def deactivateClause(self,cl_idx):
        self._status[cl_idx] = TO_DEACTIVATE
        
    def addClause(self,clause):
        if len(clause)>1:
            max_lit = (clause[0] if clause[0]>clause[1] else clause[1])|1
            self.resize(max_lit+1)
            self._unchecked_add_(clause)
                            
    def _unchecked_add_(self,clause):
        self._watcher_of[clause[0]].append(len(self._clauses))
        self._watcher_of[clause[1]].append(len(self._clauses))
        self._clauses.append(clause)
        self._status.append(ACTIVE)
        
    def _remove_watcher_(self, l, pos):
        if pos < len(self._watcher_of[l])-1:
            self._watcher_of[l][-1], self._watcher_of[l][pos] = self._watcher_of[l][pos], self._watcher_of[l][-1]
        self._watcher_of[l].pop()
        
    def __len__(self):
        return len(self.clauses)
            
    def __str__(self): 
        return self.getWatchList(range(len(self._watcher_of)/2))
        
    def getWatchList(self,atoms): 
        ostr = ''
        for a in atoms:
            for spin in (0,1):
                ostr += 'watched by '+lit_to_str(literal(a,spin))+':'
                for c in self._watcher_of[literal(a,spin)]:
                    ostr += ' '+str(self._clauses[c])
                ostr += '\n'
        return ostr
########################################
    
    


    
################################
########  CDCL  SOLVER  ########
################################
class Solver(ClauseBase,BeliefBase):
    def __init__(self, n=DEFAULT_SIZE):
        ClauseBase.__init__(self,n)
        BeliefBase.__init__(self,n)
        self._num_atoms    = n
        self._unpropagated = 0
        self._level        = 0
        self._truth        = array('I',[FALSE]*n)
        self._reason       = [None]*n
        self._asg_level    = [0]*n
        # self._activity     = [0.0]*n
        self._trail        = array('i')
        
        # statistics
        self.num_choice    = stat.Statistic('number of choices', 0)
        self.num_conflict  = stat.Statistic('number of conflicts', 0)
        self.num_propag    = stat.Statistic('number of propagations', 0)
        self.num_learnt    = stat.StatNumLearnt(self)
        self.max_activity  = stat.Statistic('maximum activity', 0)
        
        # parameters
        self._activity_increment = 1e-100
        self._activity_decay     = 1.1
        self._activity_bound     = 1e1000000
        
        
    def initActivity(self):
        """docstring for initActivity"""
        activity = [.0]*self._num_atoms
        for clause in self._clauses:
            for l in clause:
                a = atom(l)
                activity[a] += self._activity_increment/len(clause)
                if activity[a] > self.max_activity.getValue():
                    self.max_activity.setValue(activity[a])
        self._activity = ActivityHeap(activity)
                
    def decay(self):
        self._activity_increment *= self._activity_decay
        max_activity = self.max_activity.getValue()
        if self._activity_bound - self._activity_increment < max_activity:
            # for a in range(self._num_atoms):
            #     self._activity[a] = self._activity[a]/max_activity*self._activity_increment
            self._activity.scaleDown(max_activity, self._activity_increment)
            self.max_activity.setValue(self._activity_increment)
        
    def increaseActivity(self, a):
        """docstring for increaseActivity"""
        new_activity = self._activity[a] + self._activity_increment
        if (VERBOSE&DBG_ACTIVITY)>0:
            print 'increase activity of', (a+1), new_activity
        self._activity[a] = new_activity
        if new_activity > self.max_activity.getValue():
            self.max_activity.setValue(new_activity)
        # print 'end increase'
 
            
    def mostActiveAtom(self):
        a = self._activity.heappop()
        if (VERBOSE&DBG_ACTIVITY)>0:
            print 'look for most active atom', (a+1), '?'
        while self.known(a):
            if (VERBOSE&DBG_ACTIVITY)>0:
                print '  no, already set'
            a = self._activity.heappop()
            if (VERBOSE&DBG_ACTIVITY)>0:
                print ' ', (a+1), '?'
        if (VERBOSE&DBG_ACTIVITY)>0:
            print '  ok!'
        return a
        
    def checkUnitPropag(self):
        cl_idx = 0
        for clause in self._clauses:
            undef = None
            for l in clause:
                if self.lit_truth(l) == UNDEF:
                    if undef == None:
                        undef = l
                    else:
                        undef = None
                        break
                elif self.lit_truth(l) == TRUE:
                    undef = None
                    break
            if undef != None:
                print 'c'+str(cl_idx), clause, [truth_to_str(self.lit_truth(l)) for l in clause], '=>', lit_to_str(undef), 'should be propagated'
                sys.exit(1)
            cl_idx += 1
        if (VERBOSE&DBG_CHECK)>0:
            print 'unit propagation OK'
        
    def checkWatchedLiterals(self):
        for a in range(self._num_atoms):
            for spin in (0,1):
                l = literal(a,spin)
                for k in self._watcher_of[l]:
                    if self._clauses[k][0] != l and self._clauses[k][1] != l:
                        print 'c'+str(k), self._clauses[k], 'watches a wrong literal:', l
                        sys.exit(1)
        if (VERBOSE&DBG_CHECK)>0:
            print 'watched literal struct OK'
                    
    def resize(self, n):
        if n>self._num_atoms:
            ClauseBase.resize(self,2*n)
            BeliefBase.resize(self,n)
            self._truth.extend([FALSE]*(n-self._num_atoms))
            self._reason.extend([None]*(n-self._num_atoms))
            self._asg_level.extend([0]*(n-self._num_atoms))
            # self._activity.extend([.0]*(n-self._num_atoms))
            # self._fact.resize(n)
            self._num_atoms = n
            
    def learnFrom(self, conflict):
        """docstring for analyze"""
        need_explaining = [l for l in conflict]
        learned_clause = [None]
        visited = set([])
        max_level = 0
        
        if (VERBOSE&DBG_LEARNING)>0:
            print self._str__bb_()
        
        idx_max_lit = 0
        while len(need_explaining)>1:
            if (VERBOSE&DBG_LEARNING)>0:
                print "current clause:", [lit_to_str(l) for l in learned_clause[1:]]
                print "yet to explain:", [lit_to_str(l) for l in need_explaining]
            
            l = need_explaining.pop()
            a = atom(l)
            
            if (VERBOSE&DBG_LEARNING)>0:
                print 'analyze', lit_to_str(l)
            
            if not a in visited:
                visited.add(a)
                self.increaseActivity(a)
                if self._asg_level[a] < self._level:
                    if (VERBOSE&DBG_LEARNING)>0:
                        print '  no need to explain'
                    if self._asg_level[a] > max_level:
                        max_level = self._asg_level[a]
                        idx_max_lit = len(learned_clause)
                    learned_clause.append(opposite(l))
                elif self._reason[a] == None:
                    if (VERBOSE&DBG_LEARNING)>0:
                        print '  last decision'
                    need_explaining.insert(0,l)
                else:
                    if (VERBOSE&DBG_LEARNING)>0:
                        print '  explain by', [lit_to_str(p) for p in self._reason[a] if atom(p) != a and atom(p) not in visited]
                    need_explaining.extend([p for p in self._reason[a] if atom(p) != a and atom(p) not in visited])
            else:
                if (VERBOSE&DBG_LEARNING)>0:
                    print 'already explained'
                
        a = atom(need_explaining[0])
        learned_clause[0] = opposite(literal(a,self._truth[a])) 
         
        if (VERBOSE&DBG_LEARNING)>0:
            print 'learned', [lit_to_str(l) for l in learned_clause]
            print 'backjump', (self._level - max_level), 'levels'
        
        return (self._level - max_level), learned_clause
        
    def store(self,nogood):
        clause = Clause(nogood)
        if len(nogood)>1:
            self._learnts.append(len(self._clauses))
            self._unchecked_add_(clause)
        self.infer(clause[0], clause)
            
    def generate(self, conf_limit=-1):
        """docstring for generate"""
        outcome = UNDEF
        while outcome == UNDEF and (conf_limit<0 or conf_limit>self.num_conflict.getValue()):
            conflict = self.unitPropagate()
            if (VERBOSE&DBG_SEARCH)>0:
                print ''.join([' ' for i in range(self._level)]), 
                for a in range(self._num_atoms):
                    if self.atom_truth(a) != UNDEF:
                        print lit_to_str(literal(a, self._truth[a])),
                print
            
            if conflict == None:
                if (CHECKED&CHK_PROPAG)>0:
                    self.checkUnitPropag()
                if self.full():
                    outcome = TRUE
                else:
                    self.save()
                    decision = self.mostActiveAtom() #self.nextAtom()
                    l = literal(decision, self._truth[decision])
                    self.infer(l)
                    self.num_choice += 1
            elif self._level == 0:
                outcome = FALSE
            else:
                backtracks, nogood = self.learnFrom(conflict)
                for i in range(backtracks):
                    self.undo()
                self.store(nogood)
                self.num_conflict += 1

        if (VERBOSE&DBG_SEARCH)>0:
            print outcome
            
        if (CHECKED&CHK_SOLUTION)>0 and outcome == TRUE:
            self.checkSolution()     
        return outcome
        
    def restartSearch(self, base=100, factor=1.2):
        """docstring for restartSearch"""
        self.initActivity()
        rlimit = base
        outcome = UNDEF
        while outcome == UNDEF:
            print 'restart with limit', base, str(self.num_conflict)
            outcome = self.generate(conf_limit=rlimit)
            if outcome == UNDEF:
                while self._level>0:
                    self.undo()
                base = int(base * factor)
                rlimit += base
                self.forget()
        return outcome
        
                
    def getStatistics(self):
        """docstring for getStatistics"""      
        return str(self.num_choice)+'\n'+str(self.num_learnt)+'\n'+str(self.num_conflict)+'\n'+str(self.num_propag)
            
    def save(self):
        self._trail.append(self._size)
        self._level += 1
        
    def undo(self):
        self._size = self._trail.pop()
        for a in self[self._size:self._unpropagated]:
            self._activity.push(a)
        self._unpropagated = self._size
        self._level -= 1
        
    def nextAtom(self):
        """docstring for getNext"""
        return self._known[self._size]
    
    def lit_truth(self, p):
        a = atom(p)
        return self._truth[a]==spin(p) if self.known(a) else UNDEF
        
    def atom_truth(self, a):
        return self._truth[a] if self.known(a) else UNDEF
        
    def score(self, clause):
        """docstring for score"""
        return sum([self._activity[atom(l)] for l in clause])/(len(clause) * len(clause))

    def forget(self, forgetfulness=0.8):
        """docstring for forget"""
        scores = [self.score(self._clauses[c]) for c in self._learnts]
        visited = len(scores)-1        
        max_sc = max(scores)
        min_sc = min(scores)
        gap = max_sc - min_sc
        threshold = min_sc + forgetfulness * gap
        
        #invariant: the list learnts[:visited+1] has not been visited
        #           the list learnts[visited+1:] should be kept
        swap = False
        while visited>=0:
            # put the first non visited element at the back
            if swap:
                self._learnts[visited], self._learnts[-1] = self._learnts[-1], self._learnts[visited]
            # check if should keep or remove it
            if scores[visited]<threshold:
                self.deactivateClause(self._learnts.pop())
                swap = True
            visited -= 1
        
    def infer(self, p, reason=None):
        a = atom(p)
        t = spin(p)
        self.add(a)
        self._truth[a]     = t
        self._reason[a]    = reason
        self._asg_level[a] = self._level
        if (VERBOSE&DBG_SEARCH)>0:
            print ''.join([' ' for i in range(self._level)]), 'infer', lit_to_str(literal(a,t)), '(reason='+str(reason)+') ['+str(self._level)+']'
            
    def checkSolution(self):
        """docstring for checkSolution""" 
        cl_idx = 0       
        for cl in self._clauses:
            satisfied = False
            false_literals = set([])
            if (VERBOSE&DBG_CHECK)>0:
                print cl
            for l in cl:
                if self.lit_truth(l) == TRUE:
                    if l in false_literals:
                        print 'invalid solution', atom(l), 'assigned true and false'
                        sys.exit(1)
                    false_literals.add(opposite(l))
                    if (VERBOSE&DBG_CHECK)>0:
                        print lit_to_str(l), 'satisfies c'+str(cl_idx), cl
                    satisfied = True
                    break
            if not satisfied:
                if VERBOSE>-1:
                    print 'solution does not satisfy c'+str(cl_idx), cl
                return False
            cl_idx += 1
                
        for a in range(self._num_atoms):
            if self._truth[a] == UNDEF:
                if VERBOSE>-1:
                    print 'invalid solution x'+str(a)+' is not assigned'
                return False
            elif (VERBOSE&DBG_CHECK)>0:
                print lit_to_str(literal(a, self._truth[a]),''),
        if (VERBOSE&DBG_CHECK)>0:
            print
                
        return True
        
    def unitPropagate(self):
        conflict = None
        # while self._unpropagated < len(self._fact) and conflict == None:
        while self._unpropagated < self._size and conflict == None:
            # a = self._fact[self._unpropagated]
            a = self._known[self._unpropagated]
            if (VERBOSE&DBG_PROPAG)>0:
                print 'unit propagate', lit_to_str(literal(a, self._truth[a]))
                
            conflict = self.update(opposite(literal(a, self._truth[a])))
            if (CHECKED&CHK_WATCHED)>0:
                self.checkWatchedLiterals()
            
            self._unpropagated += 1
            self.num_propag += 1

        return conflict
        
    def update(self,old_watched):
        """update the watcheds when old_watched becomes false"""
        cl_idx = len(self._watcher_of[old_watched])-1
        conflict = None
        for k in reversed(self._watcher_of[old_watched]):
            if len(self._status) != len(self._clauses):
                print len(self._status), '!=', len(self._clauses)
            if len(self._status) <= k:
                print len(self._status), '<=', k
            if self._status[k] == TO_DEACTIVATE:
                self._remove_watcher_(old_watched,cl_idx)
            else:
            
                clause = self._clauses[k]

                # second = 0 if atom(old_watched) == atom(clause[1]) else 1
                second = 0 if atom(old_watched) == atom(clause[1]) else 1
                other_watched = clause[second]

                # check that the second watched is not known
                valo = self.lit_truth(other_watched)

                if valo != TRUE:
                    # look for a new watched to replace watched
                    new_watched = None
                    valn = UNDEF
                    j = len(clause)
                    while new_watched == None and j>2:
                        j -= 1
                        valn = self.lit_truth(clause[j])

                        if valn != FALSE:
                            # ok, we found a new watched
                            new_watched = clause[j]
                            clause[1-second] = new_watched
                            clause[j] = old_watched
                            # self._watcher_of[old_watched].pop(cl_idx) # we don't do that here
                            self._watcher_of[new_watched].append(k)
                            self._remove_watcher_(old_watched,cl_idx)

                    if new_watched == None:
                        # we could not find a new watched, so we prune 'second_watched'
                        # print '  there is no new watcher',
                        # new_watch_list.append(k)
                        if valo == FALSE:
                            conflict = clause
                        else:
                            self.infer(other_watched, clause)
            cl_idx -= 1
            if conflict != None:
                break
        return conflict
    
                        
    def __str__(self): 
        # ostr = 'clauses:\n'+ClauseBase.__str__(self)
        ostr = '\nassumptions = [\n'
        for a in self._known[:self._size]:
            p = literal(a, self._truth[a])
            ostr += lit_to_str(p)
            if self._reason[a] != None:
                ostr += ' because of '+str(self._reason[a])
            ostr += '\n'
        return ostr + ']'
        
    def _str__bb_(self): 
        ostr = ''
        rank = 1
        # for a in self._fact:
        for a in self._known[:self._size]:
            p = literal(a, self._truth[a])
            ostr += str(rank).rjust(3)+' '+str(self._asg_level[a]).rjust(3)+' '+lit_to_str(p).rjust(4)
            if self._reason[a] != None:
                ostr += ' '+str(self._reason[a])
            ostr += '\n'
            rank += 1
        return ostr 
        
    def read_dimacs(self, filename):
        self.comments = []
        cnffile = open(filename, 'r')
        for line in cnffile:
            data = line.split()
            if len(data)>0:
                if data[0] != 'c':
                    if data[0] == 'p':
                        num_atoms = int(data[2])
                        self.resize(num_atoms)
                    elif len(data) == 2:
                        # print 'unit', lit(int(data[0])), lit_to_str(lit(int(data[0])))
                        self.infer(lit(int(data[0])))
                        self._clauses.append(Clause([lit(int(p)) for p in data[:-1]]))
                        self._status.append(INACTIVE)
                    else:
                        self._unchecked_add_(Clause([lit(int(p)) for p in data[:-1]]))
                else:
                    self.comments.append(line)
                                  
    def write_dimacs(self, filename):
        cnffile = open(filename, 'w')
        for line in self.comments:
            cnffile.write(line)
        cnffile.write('p cnf '+str(self._num_atoms)+' '+str(len(self._clauses))+'\n')
        for clause in self._clauses:
            cnffile.write(' '.join([lit_to_str(l,'') for l in clause])+' 0\n')


if __name__ == '__main__':
  
    solver = Solver()
    
    cnffile = 'unif-c500-v250-s1228594393.cnf'
    if len(sys.argv)>1:
        cnffile = sys.argv[1]
    
    solver.read_dimacs(cnffile)
    outcome = solver.restartSearch()
    
    print 'Satisfiable' if outcome == TRUE else 'Unsatisfiable' if outcome == FALSE else 'Unknown'
    print solver.getStatistics()       


##  @}
