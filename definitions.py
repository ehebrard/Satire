#! /usr/bin/env python

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


########################################
######## MACROS AND DEFINITIONS ########
########################################
FALSE, TRUE, UNDEF = 0, 1, -1
EQUAL, BOUND = 0, 2

DEFAULT_SIZE = 8

DBG_SEARCH   = 1
DBG_PROPAG   = 2
DBG_LEARNING = 4
DBG_WATCH    = 8
DBG_CHECK    = 16
DBG_ACTIVITY = 32

CHK_SOLUTION = 1
CHK_PROPAG   = 4
CHK_WATCHED  = 8

ACTIVE        = 1
INACTIVE      = 0
TO_DEACTIVATE = -1


VERBOSE = 0 #DBG_ACTIVITY #DBG_PROPAG|DBG_LEARNING
CHECKED = CHK_SOLUTION

def atom(lit):
    return lit>>1
    
def spin(lit):
    return lit&1

def opposite(lit):
    return lit^1

def lit_to_str(p,x=''):
    return ('-' if (p&1)==FALSE else '')+x+str(p/2+1)
    
def lit_to_dimacs(p):
    return (-1 if (p&1)==FALSE else 1) * (p/2+1)
    
def lit(pi):
    return 2*(pi-1)+1 if pi>0 else 2*(-1-pi)
    
def literal(atom, truth):
    return 2*atom+truth
    
def truth_to_str(t):
    return 'true' if t==TRUE else 'false' if t==FALSE else 'undef'
########################################    
