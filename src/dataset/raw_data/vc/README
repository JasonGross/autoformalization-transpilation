#########################################################################
                           SOFTWARE FOUNDATIONS
#########################################################################

This directory contains both Coq scripts (.v files) and more readable
HTML files for Verifiable C, by Andrew W. Appel et al.,
volume [VC] of the Software Foundations series.

  - Preface.v or Preface.html
    The place to start reading, including details on how to install
    required software

  - index.html
    The book's cover page and navigation starting point

  - deps.html 
    Overview of the ordering of chapters

  - LICENSE
    Explanation of how these files may be redistributed

NOTE ABOUT VST VERSION:

Preface.v checks that you are using a version of VST that is well matched
to this textbook.   If you have installed VST by the standard Coq Platform
or by opam, then it will be found automatically in coq/lib/coq/user-contrib.
If that's the right version (as checked by Preface.v) then everything is easy.

TO USE THIS VOLUME BASED ON A CUSTOM-INSTALLED VST VERSION:
Otherwise, you may want to download a specific version from
https://github.com/PrincetonUniversity/VST   and build from sources.
In that case, your VST will not be found in user-contrib, and you should
follow these steps:

1. In this directory, "make clean" and remove Makefile.coq

2. Edit the first line of the Makefile to read,

COQMFFLAGS= -Q . VC -Q path/to/VST VST

where "path/to/VST" is whatever directory you've compiled VST in.

3. Edit the _CoqProject file to have the same -Q options.

4. If your compiled VST uses the special configuration COMPCERT=bundled,
then instead you should add one more -Q option to Makefile and _CoqProject:

COQMFFLAGS= -Q . VC -Q path/to/VST VST -Q path/to/VST/compcert compcert
