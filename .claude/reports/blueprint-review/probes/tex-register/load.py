"""Load the register exactly as render.py builds it: run render.py whole, with its output
redirected to register-rerender.md in this folder, and keep its globals. SAME_AS_DOSSIER says
whether the re-rendered Markdown equals dossiers/register.md byte for byte."""
import os, io, contextlib
HERE = os.path.dirname(os.path.abspath(__file__))
REG = os.path.normpath(os.path.join(HERE, "../register"))
RERENDER = os.path.join(HERE, "register-rerender.md")
_src = open(os.path.join(REG, "render.py")).read()
assert _src.count('"../../dossiers/register.md"') == 1
_src = _src.replace('"../../dossiers/register.md"', repr(RERENDER))
_g = {"__name__": "register_render"}
_cwd = os.getcwd()
os.chdir(REG)
try:
    with contextlib.redirect_stdout(io.StringIO()):
        exec(compile(_src, os.path.join(REG, "render.py"), "exec"), _g)
finally:
    os.chdir(_cwd)
SAME_AS_DOSSIER = open(RERENDER).read() == open(os.path.join(HERE, "../../dossiers/register.md")).read()
rows = _g["rows"]; NEG = _g["NEG"]; UNV = _g["UNV"]; CONTRA = _g["CONTRA"]
SUBJECTS = _g["SUBJECTS"]; SUBJ_NAME = _g["SUBJ_NAME"]; RANK_NAME = _g["RANK_NAME"]
is_position = _g["is_position"]; findings = _g["findings"]; positions = _g["positions"]
cnt = _g["cnt"]; DOSSIER_LIST = _g["dossiers"]; cites = _g["cites"]
