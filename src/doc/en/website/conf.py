# nodoctest
# Numerical Sage documentation build configuration file, created by
# sphinx-quickstart on Sat Dec  6 11:08:04 2008.
#
# This file is execfile()d with the current directory set to its containing dir.
#
# The contents of this file are pickled, so don't put values in the namespace
# that aren't pickleable (module imports are okay, they're removed automatically).
#
# All configuration values have a default; values that are commented out
# serve to show the default.

from sage_docbuild.conf import release
from sage_docbuild.conf import *  # NOQA

# Add any paths that contain custom static files (such as style sheets),
# relative to this directory to html_static_path. They are copied after the
# builtin static files, so a file named "default.css" will overwrite the
# builtin "default.css". html_common_static_path imported from sage_docbuild.conf
# contains common paths.
html_static_path = [] + html_common_static_path

# General information about the project.
project =  "Documentation"

# The name for this set of Sphinx documents.
html_title = project
html_short_title = project

# Output file base name for HTML help builder.
htmlhelp_basename = 'sage_documentation'

# Grouping the document tree into LaTeX files. List of tuples
# (source start file, target name, title, author, document class [howto/manual]).
latex_documents = [
  ('index', 'sage_documentation.tex', 'Documentation',
   'The Sage Development Team', 'manual'),
]

# Note that this effectively replaces the index.html generated from index.rst.
# Hence some template context variables such as 'title' are not provided to
# this "additional" index.html.
html_additional_pages = {
    'index': 'index.html',
}

