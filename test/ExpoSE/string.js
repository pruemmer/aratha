/* Copyright (c) Royal Holloway, University of London | Contact Blake Loring (blake@parsed.uk), Duncan Mitchell (Duncan.Mitchell.2015@rhul.ac.uk), or Johannes Kinder (johannes.kinder@rhul.ac.uk) for details or support | LICENSE.md for license details */

var stdargs = J$.readInput();

if (stdargs[3] == 'Hello') {

    if (!stdargs.includes('Hello')) {
        throw 'Unreachable';
    }

    throw 'Reachable'; 
}