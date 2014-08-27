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
import Satire
import definitions as _

if __name__ == '__main__':
  
    solver = Satire.Solver()

    cnffile = 'unif-c500-v250-s1228594393.cnf'
    if len(sys.argv)>1:
        cnffile = sys.argv[1]

        solver.read_dimacs(cnffile)
        outcome = solver.generate()
        print 'Satisfiable' if outcome == _.TRUE else 'Unsatisfiable' if outcome == _.FALSE else 'Unknown'
        print solver.getStatistics()
        
    
    
##  @}
