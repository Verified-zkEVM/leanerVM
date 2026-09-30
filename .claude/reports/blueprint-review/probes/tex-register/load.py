"""Load the register data exactly as render.py orders, numbers and resolves it, by running
render.py's own code up to the point where it starts writing Markdown."""
import os
HERE = os.path.dirname(os.path.abspath(__file__))
REG = os.path.normpath(os.path.join(HERE, "../register"))
_src = open(os.path.join(REG, "render.py")).read()
_cut = _src.index('out = [HEADER.rstrip(), ""]')
_g = {"__name__": "register_render"}
_cwd = os.getcwd()
os.chdir(REG)
try:
    exec(compile(_src[:_cut], os.path.join(REG, "render.py"), "exec"), _g)
finally:
    os.chdir(_cwd)
rows = _g["rows"]; NEG = _g["NEG"]; UNV = _g["UNV"]; CONTRA = _g["CONTRA"]
SUBJECTS = _g["SUBJECTS"]; SUBJ_NAME = _g["SUBJ_NAME"]; RANK_NAME = _g["RANK_NAME"]
is_position = _g["is_position"]
# CONTRA is not passed through res() by render.py; it is printed as is.
