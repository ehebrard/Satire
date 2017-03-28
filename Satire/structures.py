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


from array import *
        
################################################
########  IMPLEMENTATION OF SPARSE SET  ########
################################################
class BeliefBase:        
    def __init__(self,n,elts=[]):
        self._known = array('I',range(n))
        self._index = array('I',range(n))
        self._size = 0
        self._iter = 0
        for elt in elts:
            self.add(elt)
        
    def __str__(self):
        """docstring for fname"""
        ostr = str([int(self._known[i]) for i in range(self._size)])
        return ostr

    def __len__(self):
        return self._size
        
    def __iter__(self):
        self._iter = 0
        return self
        
    def next(self):
        if self._iter == self._size:
            raise StopIteration
        self._iter += 1
        return self._known[self._iter-1]
        
    # def full(self):
    #     """docstring for full"""
    #     return self._size == len(self._known)
        
    def num_choices(self):
        """docstring for full"""
        return len(self._known) - self._size
         
    def resize(self, n):
        capacity = len(self._known)
        extension = range(capacity,n)
        self._known.extend(extension)
        self._index.extend(extension)
                
    def capacity(self):
        return len(self._known)
        
    def add(self,x):
        """docstring for add"""
        if x >= len(self._index):
            self._index.extend(range(len(self._index),x+1))
            self._known.extend(range(len(self._known),x+1))
        if self._index[x] > self._size:
            tmp = self._known[self._size]
            self._known[self._size] = self._known[self._index[x]]
            self._known[self._index[x]] = tmp
            self._index[tmp] = self._index[x]
            self._index[x] = self._size
        self._size += 1
        
    def rem(self,x):
        """docstring for add"""
        if x < len(self._index):
            self._size -= 1  
            if self._index[x] < self._size:
                tmp = self._known[self._size]
                self._known[self._size] = self._known[self._index[x]]
                self._known[self._index[x]] = tmp
                self._index[tmp] = self._index[x]
                self._index[x] = self._size     
                
    def known(self, atom):
        return self._index[atom]<self._size
        
    def __getitem__(self, i):
        return self._known.__getitem__(i)

    def __getslice__(self, i, j):
        return self._known.__getslice__(i, j)
        
    def checkIntegrity(self):
        """docstring for checkIntegrity"""
        if len(self._known) != len(self._index):
            print "Inconsistent array size!!"
            sys.exit(1)
        for i in range(len(self._known)):
            x = self._known[i]
            if x > len(self._index):
                print "Element too big:", x
                sys.exit(1)
            if self._index[x] != i:
                print "Inconsistent indexing!!"
                sys.exit(1)
        for x in range(len(self._index)):
            i = self._index[x]
            if i > len(self._known):
                print "Index too big:", i
                sys.exit(1)
                if self._known[i] != x:
                    print "Inconsistent indexing!!"
                    sys.exit(1)   
        print 'ok'
################################################


from itertools import islice, count, imap, izip, tee, chain
from operator import itemgetter


###################################################################################
########  HEAP OF INTEGER IN [0..n-1] ORDERED BY FLOATING POINT PRIORITIES ########
###################################################################################
## heap is the list (in heap order) of entries [prio,elt], elt must be an int 
## index gives the current position of an element in the heap
## prio gives the priority of an item (used for ordering)
class ActivityHeap(array):
    def __new__(cls, data):
        """docstring for __init__"""
        newme = array.__new__(cls, 'i', range(len(data)))
        newme._index = array('i', newme)
        newme._prio = array('d', data)
        newme.heapify()
        return newme
                
    def push(self, entry):
        """Push item onto heap, maintaining the heap invariant."""
        if self._index[entry]<0:
            self._index[entry] = len(self)
            self.append(entry) 
            self._siftdown(0, len(self)-1)
        # self.checkIntegrity()

    def __setitem__(self, item, prio):
        # print 'before update'
        # self.checkIntegrity()
        pos = self._index[item]
        self._prio[item] = prio
        if pos>0:
            self._siftdown(0, pos)
        # print 'after update'
        # self.checkIntegrity()
        return self
        
    def __getitem__(self, item):
        return self._prio[item]

    def heappop(self):
        """Pop the smallest item off the heap, maintaining the heap invariant."""
        lastelt = self.pop()    # raises appropriate IndexError if heap is empty
        if self:
            returnitem = array.__getitem__(self,0)
            array.__setitem__(self,0,lastelt)
            self._siftup(0)
        else:
            returnitem = lastelt
        self._index[returnitem] = -1
        # self.checkIntegrity()
        return returnitem

    def heapify(self):
        """Transform list into a heap, in-place, in O(len(x)) time."""
        n = len(self)
        # Transform bottom-up.  The largest index there's any point to looking at
        # is the largest with a child index in-range, so must have 2*i + 1 < n,
        # or i < (n-1)/2.  If n is even = 2*j, this is (2*j-1)/2 = j-1/2 so
        # j-1 is the largest, which is n//2 - 1.  If n is odd = 2*j+1, this is
        # (2*j+1-1)/2 = j so j-1 is the largest, and that's again n//2-1.
        for i in reversed(xrange(n//2)):
            self._siftup(i)
        # self.checkIntegrity()

    # 'heap' is a heap at all indices >= startpos, except possibly for pos.  pos
    # is the index of a leaf with a possibly out-of-order value.  Restore the
    # heap invariant.
    def _siftdown(self, startpos, pos):
        newitem = array.__getitem__(self,pos)
        # Follow the path to the root, moving parents down until finding a place
        # newitem fits.
        while pos > startpos:
            parentpos = (pos - 1) >> 1
            parent = array.__getitem__(self,parentpos)
            if self._prio[newitem] > self._prio[parent]:
                array.__setitem__(self,pos,parent)
                self._index[parent] = pos
                pos = parentpos
                continue
            break
        array.__setitem__(self,pos,newitem)
        self._index[newitem] = pos


    
    # The child indices of heap index pos are already heaps, and we want to make
    # a heap at index pos too.  We do this by bubbling the smaller child of
    # pos up (and so on with that child's children, etc) until hitting a leaf,
    # then using _siftdown to move the oddball originally at index pos into place.
    #
    # We *could* break out of the loop as soon as we find a pos where newitem <=
    # both its children, but turns out that's not a good idea, and despite that
    # many books write the algorithm that way.  During a heap pop, the last array
    # element is sifted in, and that tends to be large, so that comparing it
    # against values starting from the root usually doesn't pay (= usually doesn't
    # get us out of the loop early).  See Knuth, Volume 3, where this is
    # explained and quantified in an exercise.
    #
    # Cutting the # of comparisons is important, since these routines have no
    # way to extract "the priority" from an array element, so that intelligence
    # is likely to be hiding in custom __cmp__ methods, or in array elements
    # storing (priority, record) tuples.  Comparisons are thus potentially
    # expensive.
    #
    # On random arrays of length 1000, making this change cut the number of
    # comparisons made by heapify() a little, and those made by exhaustive
    # heappop() a lot, in accord with theory.  Here are typical results from 3
    # runs (3 just to demonstrate how small the variance is):
    #
    # Compares needed by heapify     Compares needed by 1000 heappops
    # --------------------------     --------------------------------
    # 1837 cut to 1663               14996 cut to 8680
    # 1855 cut to 1659               14966 cut to 8678
    # 1847 cut to 1660               15024 cut to 8703
    #
    # Building the heap by using heappush() 1000 times instead required
    # 2198, 2148, and 2219 compares:  heapify() is more efficient, when
    # you can use it.
    #
    # The total compares needed by list.sort() on the same lists were 8627,
    # 8627, and 8632 (this should be compared to the sum of heapify() and
    # heappop() compares):  list.sort() is (unsurprisingly!) more efficient
    # for sorting.

    def _siftup(self, pos):
        endpos = len(self)
        startpos = pos
        newitem = array.__getitem__(self,pos)
        # Bubble up the smaller child until hitting a leaf.
        childpos = 2*pos + 1    # leftmost child position
        while childpos < endpos:
            # Set childpos to index of smaller child.
            rightpos = childpos + 1
            if rightpos < endpos and self._prio[array.__getitem__(self,childpos)] <= self._prio[array.__getitem__(self,rightpos)]:
                childpos = rightpos
            # Move the smaller child up.
            array.__setitem__(self,pos,array.__getitem__(self,childpos))
            self._index[array.__getitem__(self,pos)] = pos
            pos = childpos
            childpos = 2*pos + 1
        # The leaf at pos is empty now.  Put newitem there, and bubble it up
        # to its final resting place (by sifting its parents down).
        array.__setitem__(self,pos,newitem)
        self._index[newitem] = pos
        self._siftdown(startpos, pos)


    def scalePriority(self, div, mul):
        """docstring for scalePriority"""
        for i in range(len(self)):
            self._prio[i] = self._prio[i] * mul / div
            
            
    def checkIntegrity(self):
        import sys
        """docstring for checkIntegrity"""
        itemset = set([])
        for i in range(len(self)):
            item = array.__getitem__(self, i)
            itemset.add(item)
            print str(i).rjust(3), str(item).rjust(3), str(self._index[item]).rjust(3)
            if self._index[item] != i:
                print 'wrong indexing!'
                sys.exit(1)
        for item in range(len(self._index)):
            idx = self._index[item]
            if idx>=0 and item not in itemset:
                print 'wrong membership!'
                sys.exit(1)   
###################################################################################



        
if __name__ == '__main__':  
        
    # q = ActivityQueue([(1.7,1), (3.2,2), (2.5,3), (7.7,4), (7.6,5), (8.9,6), (10,7), (1.9,8)])
    q = ActivityHeap([1.7, 3.2, 2.5, 7.7, 7.6, 8.9, 10, 1.9])
    # heapify(q)
    
    for a in q:
        print a,q[a], '  ',
    print
    print


    q[7] = 9.3
    
    
    for a in q:
        print a,q[a], '  ',
    print
    print
    
    
    while q:
        a = q.heappop()
        print a,q[a], '  ',
    print
    print
        
    for a in range(8):
        q.push(a)    
    
    for a in q:
        print a,q[a], '  ',
    print
    print
    
    
    while q:
        a = q.heappop()
        print a,q[a], '  ',
    print



  
