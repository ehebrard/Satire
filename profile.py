#! /usr/bin/env python

import sys
import cProfile

from Satire import *


if __name__ == '__main__':
  
    solver = Solver()
    
    cnffile = 'cnf_example/unif-c1225-v350-s655749504.cnf'
    if len(sys.argv)>1:
        cnffile = sys.argv[1]
    
    solver.readDimacs(cnffile)

    
    cProfile.run('solver.restartSearch()')
    

