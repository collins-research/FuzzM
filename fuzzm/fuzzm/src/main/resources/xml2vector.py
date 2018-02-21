#!/usr/bin/env python
 
## Copyright (C) 2017, Rockwell Collins
## All rights reserved.
##
## This software may be modified and distributed under the terms
## of the 3-clause BSD license.  See the LICENSE file for details.
## 
##

from collections import defaultdict
import xml.etree.ElementTree
import sys

## This script transforms a JKind .xml file into a .vector
## file consisting of a simple sequence of input values and
## a .funs file containing a description of the UF values.

## We should probably modify jkind (or our interface to it) to
## generate inputs directly.

def extractInputSignals(inputs,signals):
    res = defaultdict(lambda: defaultdict(int))
    for signal in signals:
        name = signal.get('name')
        values = signal.findall('Value')
        for value in values:
            res[int(value.get('time'))][name] = value.text
    return res

def dumpVector(vec,fp):
    fp.write(" ".join(vec) + "\n")

def processFunctions(functions,ffp):
    for function in functions:
        inputs = function.findall('Input')
        output = function.find('Output')
        name = function.get('name')
        for functionvalue in function.findall('FunctionValue'):
            ffp.write(name + " " + output.get('type') + " " + functionvalue.get('value'))
            for arg in functionvalue.findall('ArgumentValue'):
                argspec = function.find('Input[@name="' + arg.get('name') + '"]')
                argtype = argspec.get('type')
                ffp.write(" " + argtype + " " + arg.get('value'))
            ffp.write("\n")

## Print all of the falsifiable properties

def processRoot(inputs,root,vfp,ffp):
    ## dumpVector(inputs,vfp)
    for child in root.findall('Property'):
        ans = child.find('Answer')
        if (ans.text == 'falsifiable'):
            tr = child.find('Counterexample')
            ## print ";; Property", child.get('name')
            sigs = extractInputSignals(inputs,tr.findall('Signal'))
            for step in range(0,len(sigs.keys())):
                vector = sigs[step]
                keys = vector.keys()
                missing = [input for input in inputs if input not in keys]
                if missing:
                    print "Missing Inputs : " + str(missing)
                    assert(False)
                values = [vector[input] for input in inputs]
                dumpVector(values,vfp)
            processFunctions(tr.findall('Function'),ffp)

## root = xml.etree.ElementTree.parse('main.xml').getroot()
## inputs = ['sub','data','done']
## processRoot(inputs,root)

def processFile(model):
    ifile = model + ".inputs"
    with open(ifile) as f:
        inputs = f.read().split()
    xfile = model + ".xml"
    root = xml.etree.ElementTree.parse(xfile).getroot()
    vfile = model + ".vector"
    ffile = model + ".funs"
    with open(vfile,'w') as vfp:
        with open(ffile,'w') as ffp:
            processRoot(inputs,root,vfp,ffp)

def main():
    if (len(sys.argv) != 2):
        print "Usage: xml2vector.py module"
        exit(1)
    processFile(sys.argv[1])

if __name__ == '__main__':
    main()
