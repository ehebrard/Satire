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


################################################
########  GENERIC CLASS FOR PARAMETERS  ########
################################################   
class Parameter:
    """docstring for Parameter"""
    def __init__(self, name_, value_):
        self._name = name_
        self._value = value_
                
    def getValue(self):
        self.update()
        return self._value
        
    def setValue(self, newval):
        self._value = newval
        
    def __iadd__(self, incr):
        self._value += incr
        return self
        
    def __isub__(self, incr):
        self._value -= incr
        return self
        
    def __imul__(self, incr):
        self._value *= incr
        return self
        
    def __idiv__(self, incr):
        self._value /= incr
        return self
    
    def getName(self):
        return self._name
        
    def __str__(self):
        """docstring for __str__"""
        return self.getName()+' = '+str(self.getValue())
################################################
