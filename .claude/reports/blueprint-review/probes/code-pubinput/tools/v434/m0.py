# Baseline: the module with only the namespace changed.
EDITS = []
TAIL = """
open LeanerVM.Protocol.@NS@ in
#print axioms publicInputSecurity
open LeanerVM.Protocol.@NS@ in
#print axioms publicInputComplete
"""
