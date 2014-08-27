#! /usr/bin/env python

import sys
import cProfile

from NumSAT import *


if __name__ == '__main__':
  
    solver = SatSolver()
    
    cnffile = '../../dev/git/Mistral-2.0/cnf/gen-1.2/unif-c875-v250-s1352423948.cnf'
    if len(sys.argv)>1:
        cnffile = sys.argv[1]
    
    solver.read_dimacs(cnffile)

    
    cProfile.run('solver.generate()')
    

