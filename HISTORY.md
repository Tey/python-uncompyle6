This project has history of over 17 years spanning back to Python 1.5

There have been a number of people who have worked on this. I am awed
by the amount of work, number of people who have contributed to this,
and the cleverness in the code.

The below is an annotated history from my reading of the sources cited.

In 1998, John Aycock first wrote a grammar parser in Python,
eventually called SPARK, that was usable inside a Python program. This
code was described in the
[7th International Python Conference](http://legacy.python.org/workshops/1998-11/proceedings/papers/aycock-little/aycock-little.html). That
paper doesn't talk about decompilation, nor did John have that in mind
at that time. It does mention that a full parser for Python (rather
than the simple languages in the paper) was being considered.

[This](http://pages.cpsc.ucalgary.ca/~aycock/spark/content.html#contributors)
contains a of people acknowledged in developing SPARK. What's amazing
about this code is that it is reasonably fast and has survived up to
Python 3 with relatively little change. This work was done in
conjunction with his Ph.D Thesis. This was finished around 2001. In
working on his thesis, John realized SPARK could be used to deparse
Python bytecode. In the fall of 1999, he started writing the Python
program, "decompyle", to do this.

This code introduced another clever idea: using table-driven
semantics routines, using format specifiers.

The last mention of a release of SPARK from John is around 2002.

In the fall of 2000, Hartmut Goebel
[took over maintaining the code](https://groups.google.com/forum/#!searchin/comp.lang.python/hartmut$20goebel/comp.lang.python/35s3mp4-nuY/UZALti6ujnQJ). The
first subsequennt public release announcement that I can find is
["decompyle - A byte-code-decompiler version 2.2 beta 1"](https://mail.python.org/pipermail/python-announce-list/2002-February/001272.html).

From the CHANGES file found in
[the tarball for that release](http://old-releases.ubuntu.com/ubuntu/pool/universe/d/decompyle2.2/decompyle2.2_2.2beta1.orig.tar.gz),
it appears that Hartmut did most of the work to get this code to
accept the full Python language. He added precidence to the table
specifiers, support for multiple versions of Python, the
pretty-printing of docstrings, lists and hashes. He also wrote
extensive tests and routines to the testing and verification of
decompiled bytecode.

decompyle2.2 was packaged for Debian (sarge) by
[Ben Burton around 2002](https://packages.qa.debian.org/d/decompyle.html). As
it worked on Python 2.2 only long after Python 2.3 and 2.4 were in
widespread use, it was removed.

[Crazy Compilers](http://www.crazy-compilers.com/decompyle/) offers a
byte-code decompiler service for versions of Python up to 2.6. As
someone who worked in compilers, it is tough to make a living by
working on compilers. (For example, based on
[John Aycock's recent papers](http://pages.cpsc.ucalgary.ca/~aycock/)
it doesn't look like he's done anything compiler-wise since SPARK). So
I hope people will use the crazy-compilers service. I wish them the
success that his good work deserves.

Next we get to
["uncompyle" and PyPI](https://pypi.python.org/pypi/uncompyle/1.1) and
the era of git repositories. In contrast to decompyle, this now runs
only on Python 2.7 although it accepts bytecode back to Python
2.5. Thomas Grainger is the package owner of this, although Hartmut is
listed as the author.

The project exists not only on
[github](https://github.com/gstarnberger/uncompyle) but also on
[bitbucket](https://bitbucket.org/gstarnberger/uncompyle) where the
git history goes back to 2009. Somewhere in there the name was changed
from "decompyle" to "uncompyle".

The name Thomas Grainger isn't found in (m)any of the commits in the
several years of active development. Guenther Starnberger, Keknehv,
hamled, and Eike Siewertsen are principle committers here.

This project, uncompyle6, however owes its existence to uncompyle2 by
Myst herie (Mysterie) whose first commit seems to goes back to 2012;
it is also based on Hartmut's code. I chose this as it seems had been
the most actively worked on most recently.

Over the many years, code styles and Python features have
changed. However brilliant the code was and still is, it hasn't really
had a single public active maintainer. And there have been many forks
of the code.

That it has been in need of an overhaul has been recognized by the
Hartmut a decade an a half ago:

[decompyle/uncompile__init__.py](https://github.com/gstarnberger/uncompyle/blob/master/uncompyle/__init__.py#L25-L26)

    NB. This is not a masterpiece of software, but became more like a hack.
    Probably a complete rewrite would be sensefull. hG/2000-12-27

One of the attempts to modernize it and make it available for Python3
is [the one by Anton Vorobyov (DarkFenX)](https://github.com/DarkFenX/uncompyle3). I've
followed some of the ideas there in this project.

Lastly, I should mention [unpyc](https://code.google.com/p/unpyc3/)
and most especially [pycdc](https://github.com/zrax/pycdc), largely by
Michael Hansen and Darryl Pogue. If they supported getting source-code
fragments and I could call it from Python, I'd probably ditch this and
use that. From what I've seen, the code runs blindingly fast and spans
all versions of Python.

Tests for the project have been, or are being, culled from all of the
projects mentioned.

NB. If you find mistakes, want corrections, or want your name added (or removed),
please contact me.