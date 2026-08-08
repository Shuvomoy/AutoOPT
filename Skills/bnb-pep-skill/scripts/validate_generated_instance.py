#!/usr/bin/env python3
"""Static-lint generated BnB-PEP derivation and Julia artifacts.

All checks are document-wide phrase-presence checks (static lint), not
per-section structural validation and not computational verification.
"""

from __future__ import annotations

import argparse
import re
import sys
import tempfile
from pathlib import Path


DERIVATION_REQUIREMENTS = {
    "formalized instance": [r"formalized instance", r"function class"],
    "outer design problem": [r"outer .*problem", r"method parameter"],
    "inner worst-case problem": [r"inner .*worst", r"fixed parameter"],
    "infinite-dimensional problem": [r"infinite-dimensional"],
    "interpolation reduction": [r"interpolation"],
    "finite-dimensional maximization": [r"finite-dimensional"],
    "gramian primal SDP": [r"gramian", r"primal .*sdp"],
    "dual SDP": [r"dual .*sdp"],
    "strong duality": [r"strong duality"],
    "stage 2 local problem": [
        r"stage\s*2|local .*problem|local .*model|qcqp",
        r"Lem:quadratic-characterization-psd-1|P\s*P\s*\^\s*\\?top|P\s*\*\s*P'",
    ],
    "stage 1/2 implementation plan": [r"implementation plan"],
    "implementation mapping": [r"mapping checklist|derivation-to-julia"],
    "approval gate": [r"approval|approve"],
}

# label -> (pattern, flags). Flags are deliberately per-pattern: line and case
# scoping prevent false positives on ordinary comments, such as a policy
# remark mentioning Gurobi or the word "nonconvex", which is unavoidable
# domain vocabulary in generated BnB-PEP artifacts.
FORBIDDEN_JULIA_PATTERNS = {
    "global solution option": (r"find_globally_optimal", re.IGNORECASE),
    "Gurobi optimizer": (r"Gurobi\s*\.\s*Optimizer", 0),
    "Gurobi package import": (
        r"\busing\b[^\n]*\bGurobi\b|\bimport\b[^\n]*\bGurobi\b",
        0,
    ),
    "Gurobi nonconvex attribute": (r"\"NonConvex\"", 0),
    "Gurobi MIP gap": (r"\"MIPGap\"", 0),
    "spatial branch-and-bound API": (
        r"\b(?:spatial_branch_and_bound|spatialBranchAndBound|branch_and_bound|branchAndBound)\s*\(",
        re.IGNORECASE,
    ),
    "Stage 3 routine": (
        r"\b(?:(?:run|solve)_stage_?3(?:_[A-Za-z0-9_]+)?|stage_?3_(?:global|branch)(?:_[A-Za-z0-9_]+)?)\b",
        re.IGNORECASE,
    ),
    "global optimizer status": (
        r"MOI\s*\.\s*OPTIMAL[^\n]*find_globally_optimal",
        re.IGNORECASE,
    ),
    "unconditional MosekTools import": (
        r"(?m)^(?:using|import)\s+[^\n]*\bMosekTools\b",
        0,
    ),
    "unconditional Mosek import": (
        r"(?m)^(?:using|import)\s+[^\n]*\bMosek\b",
        0,
    ),
    "unconditional KNITRO import": (
        r"(?m)^(?:using|import)\s+[^\n]*\bKNITRO\b",
        0,
    ),
}

STAGE3_GLOBAL_ALLOWED_LABELS = {
    "global solution option",
    "Gurobi optimizer",
    "Gurobi package import",
    "Gurobi nonconvex attribute",
    "Gurobi MIP gap",
    "spatial branch-and-bound API",
    "Stage 3 routine",
    "global optimizer status",
}

STAGE3_GLOBAL_REQUIREMENTS = {
    "explicit Stage 3 opt-in gate": [
        r"explicit[_ -]?stage3[_ -]?request|explicit.*stage\s*3|user explicitly (?:asks|requested)",
    ],
    "Stage 3 default horizon N = 1": [
        r"stage\s*3|stage3|global",
        r"stage3_default_N\s*=\s*1|stage3_default_horizon\s*=\s*1|N\s*=\s*1",
    ],
    "larger horizons require explicit override": [
        r"larger .*horizon.*explicit|explicit.*override|horizon_override",
    ],
    "solver-evidence-only status": [
        r"solver evidence",
        r"not .*theorem|not theorem-level proof|not .*proof|not .*Lean",
    ],
    "solver name and version": [
        r"solver.*version|solver_name|solver_version",
    ],
    "termination status": [
        r"termination_status|termination status",
    ],
    "incumbent objective": [
        r"incumbent",
    ],
    "best bound or lower bound": [
        r"best_bound|best bound|global lower bound|\bbound\b",
    ],
    "gap or MIPGap": [
        r"MIPGap|MIP gap|\bgap\b",
    ],
    "feasibility and optimality tolerances": [
        r"feasibility.*tolerance|optimality.*tolerance|tolerances",
    ],
    "time limit": [
        r"time_limit|time limit",
    ],
    "branching status": [
        r"branching_status|branching status|node_count|node count",
    ],
    "logs and artifacts": [
        r"log_path|log path|logs?",
        r"artifact",
    ],
}


def _read(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        return path.read_text()


def validate_derivation(path: Path) -> list[str]:
    text = _read(path)
    folded = text.lower()
    errors: list[str] = []
    for label, patterns in DERIVATION_REQUIREMENTS.items():
        if not all(re.search(pattern, folded, re.IGNORECASE | re.DOTALL) for pattern in patterns):
            errors.append(f"Missing or incomplete derivation requirement: {label}")
    return errors


def validate_julia(path: Path, allow_stage3_global: bool = False) -> list[str]:
    text = _read(path)
    errors: list[str] = []
    for label, (pattern, flags) in FORBIDDEN_JULIA_PATTERNS.items():
        if allow_stage3_global and label in STAGE3_GLOBAL_ALLOWED_LABELS:
            continue
        if re.search(pattern, text, flags):
            errors.append(f"Disallowed Julia/global-solver pattern found: {label}")

    required_patterns = {
        "JuMP model": r"\bModel\s*\(",
        "primal SDP routine": r"solve_primal_pep|primal.*sdp",
        "dual SDP routine": r"solve_dual_pep|dual.*sdp",
        "local Stage 2 routine": r"solve_bnb_pep|stage.*2|local.*solve|locally_optimal|Ipopt|KNITRO",
        "smoke horizons N = 1,2,3,4,5": (
            r"N\s*=\s*1\s*,\s*2\s*,\s*3\s*,\s*4\s*,\s*5|"
            r"for\s+N\s+in\s+1\s*:\s*5|"
            r"for\s+N\s+in\s*\[\s*1\s*,\s*2\s*,\s*3\s*,\s*4\s*,\s*5\s*\]|"
            r"for\s+N\s+in\s*\(\s*1\s*,\s*2\s*,\s*3\s*,\s*4\s*,\s*5\s*\)|"
            r"Ns\s*=\s*1\s*:\s*5"
        ),
    }
    for label, pattern in required_patterns.items():
        if not re.search(pattern, text, re.IGNORECASE | re.DOTALL):
            errors.append(f"Missing expected Julia component: {label}")
    if allow_stage3_global:
        for label, patterns in STAGE3_GLOBAL_REQUIREMENTS.items():
            if not all(re.search(pattern, text, re.IGNORECASE | re.DOTALL) for pattern in patterns):
                errors.append(f"Missing opt-in Stage 3 requirement: {label}")
    return errors


def self_test() -> int:
    good_md = """# Formalized Instance
Function class.
# Outer Design Problem
Method parameters.
# Inner Worst-Case Problem for Fixed Parameters
Fixed parameters.
# Infinite-Dimensional Inner Problem
# Interpolation Reduction
# Finite-Dimensional Maximization
# Gramian Formulation and Primal SDP
# Dual SDP
# Strong Duality
# Stage 2 Local Nonlinear Design Problem
Use Lem:quadratic-characterization-psd-1.
# Stage 1/2 Implementation Plan
Stage 1 solves the dual SDP; Stage 2 warm-starts the local solve.
# Derivation-to-Julia Mapping Checklist
# Approval Gate
Approve before Julia.
"""
    bad_jl = "using JuMP, Gurobi\nmodel = Model(Gurobi.Optimizer)\nsolution_type = :find_globally_optimal\n"
    bad_stage3_jl = """using JuMP
function solve_primal_pep()
    model = Model()
end
function solve_dual_pep()
    model = Model()
end
function solve_bnb_pep()
    model = Model()
end
function solve_stage3_global()
end
function run_smoke_tests()
    for N in 1:5
    end
end
"""
    good_jl = """using JuMP
# This generated artifact does not run global branch-and-bound.
function solve_primal_pep()
    model = Model()
end
function solve_dual_pep()
    model = Model()
end
function solve_bnb_pep()
    model = Model()
end
function run_smoke_tests()
    for N in 1:5
        solve_primal_pep()
        solve_dual_pep()
        solve_bnb_pep()
    end
end
"""
    # Policy comments and domain vocabulary must NOT trip the forbidden
    # patterns, and the canonical keyword-argument smoke wrapper
    # (Ns = 1:5 with `for N in Ns`) must satisfy the smoke-horizon check.
    good_comments_jl = """using JuMP
# Policy: this artifact never requires Gurobi, and the Stage 2 model solves a
# nonconvex local problem with Ipopt warm-started from the dual SDP.
function solve_primal_pep()
    model = Model()
end
function solve_dual_pep()
    model = Model()
end
function solve_bnb_pep()
    model = Model()
end
function run_stage1_stage2_smoke_tests(; Ns = 1:5)
    for N in Ns
        solve_primal_pep()
        solve_dual_pep()
        solve_bnb_pep()
    end
end
"""
    bad_attribute_jl = """using JuMP
function solve_primal_pep()
    model = Model()
    set_optimizer_attribute(model, "NonConvex", 2)
end
function solve_dual_pep()
    model = Model()
end
function solve_bnb_pep()
    model = Model()
end
function run_smoke_tests()
    for N in 1:5
    end
end
"""
    bad_optional_solver_jl = """using JuMP, MosekTools
function solve_primal_pep()
    model = Model()
end
function solve_dual_pep()
    model = Model()
end
function solve_bnb_pep()
    model = Model()
end
function run_smoke_tests()
    for N in 1:5
    end
end
"""
    good_conditional_solver_jl = """using JuMP
function default_sdp_optimizer()
    if Base.find_package("MosekTools") !== nothing
        @eval import MosekTools
        return MosekTools.Optimizer
    end
    return nothing
end
function solve_primal_pep()
    model = Model()
end
function solve_dual_pep()
    model = Model()
end
function solve_bnb_pep()
    model = Model()
end
function run_smoke_tests()
    for N in 1:5
    end
end
"""
    good_stage3_global_jl = """using JuMP, Gurobi
# Explicit Stage 3 opt-in: user explicitly requested BnB-PEP Stage 3.
# Stage 3 default horizon: stage3_default_N = 1.
# Larger Stage 3 horizons require explicit override via horizon_override.
# Solver evidence only: not theorem-level proof and not Lean verification.
# Evidence fields: solver_name, solver_version, termination_status,
# incumbent_objective, best_bound, MIPGap gap, feasibility tolerance,
# optimality tolerance, time_limit, branching_status, node_count, log_path,
# input_artifact, output_artifact.
function solve_primal_pep()
    model = Model()
end
function solve_dual_pep()
    model = Model()
end
function solve_bnb_pep()
    model = Model()
end
function solve_stage3_global(; explicit_stage3_request::Bool = false, N = 1, horizon_override::Bool = false)
    @assert explicit_stage3_request "BnB-PEP Stage 3 requires explicit opt-in."
    @assert N == 1 || horizon_override "Larger Stage 3 horizons require explicit override."
    model = Model(Gurobi.Optimizer)
    solution_type = :find_globally_optimal
    set_optimizer_attribute(model, "NonConvex", 2)
    set_optimizer_attribute(model, "MIPGap", 1e-2)
    if termination_status(model) == MOI.OPTIMAL && solution_type == :find_globally_optimal
        return (; solver_name = "Gurobi", solver_version = "recorded separately",
                termination_status = "OPTIMAL", incumbent_objective = NaN,
                best_bound = NaN, gap = NaN, time_limit = NaN,
                branching_status = "recorded separately",
                log_path = "stage3.log", output_artifact = "stage3.json")
    end
end
function run_stage1_stage2_smoke_tests(; Ns = 1:5)
    for N in Ns
        solve_primal_pep()
        solve_dual_pep()
        solve_bnb_pep()
    end
end
"""
    bad_stage3_missing_evidence_jl = """using JuMP, Gurobi
function solve_primal_pep()
    model = Model()
end
function solve_dual_pep()
    model = Model()
end
function solve_bnb_pep()
    model = Model()
end
function solve_stage3_global(; N = 1)
    model = Model(Gurobi.Optimizer)
    solution_type = :find_globally_optimal
end
function run_smoke_tests()
    for N in 1:5
    end
end
"""
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        md_path = root / "derivation.md"
        bad_jl_path = root / "bad.jl"
        bad_stage3_jl_path = root / "bad_stage3.jl"
        good_jl_path = root / "good.jl"
        good_comments_jl_path = root / "good_comments.jl"
        bad_attribute_jl_path = root / "bad_attribute.jl"
        bad_optional_solver_jl_path = root / "bad_optional_solver.jl"
        good_conditional_solver_jl_path = root / "good_conditional_solver.jl"
        good_stage3_global_jl_path = root / "good_stage3_global.jl"
        bad_stage3_missing_evidence_jl_path = root / "bad_stage3_missing_evidence.jl"
        md_path.write_text(good_md)
        bad_jl_path.write_text(bad_jl)
        bad_stage3_jl_path.write_text(bad_stage3_jl)
        good_jl_path.write_text(good_jl)
        good_comments_jl_path.write_text(good_comments_jl)
        bad_attribute_jl_path.write_text(bad_attribute_jl)
        bad_optional_solver_jl_path.write_text(bad_optional_solver_jl)
        good_conditional_solver_jl_path.write_text(good_conditional_solver_jl)
        good_stage3_global_jl_path.write_text(good_stage3_global_jl)
        bad_stage3_missing_evidence_jl_path.write_text(bad_stage3_missing_evidence_jl)
        if validate_derivation(md_path):
            print("self-test failed: valid derivation was rejected", file=sys.stderr)
            return 1
        if not validate_julia(bad_jl_path):
            print("self-test failed: invalid Julia was accepted", file=sys.stderr)
            return 1
        if not validate_julia(bad_stage3_jl_path):
            print("self-test failed: Stage 3 Julia was accepted", file=sys.stderr)
            return 1
        if not validate_julia(bad_attribute_jl_path):
            print("self-test failed: Gurobi NonConvex attribute was accepted", file=sys.stderr)
            return 1
        if not validate_julia(bad_optional_solver_jl_path):
            print("self-test failed: unconditional optional solver import was accepted", file=sys.stderr)
            return 1
        if validate_julia(good_jl_path):
            print("self-test failed: valid Julia was rejected", file=sys.stderr)
            return 1
        if validate_julia(good_comments_jl_path):
            print("self-test failed: policy comments or the Ns = 1:5 wrapper were rejected", file=sys.stderr)
            return 1
        if validate_julia(good_conditional_solver_jl_path):
            print("self-test failed: conditional optional solver loading was rejected", file=sys.stderr)
            return 1
        if not validate_julia(good_stage3_global_jl_path):
            print("self-test failed: opt-in Stage 3 Julia was accepted by default lint", file=sys.stderr)
            return 1
        if validate_julia(good_stage3_global_jl_path, allow_stage3_global=True):
            print("self-test failed: opt-in Stage 3 Julia was rejected by opt-in lint", file=sys.stderr)
            return 1
        if not validate_julia(bad_stage3_missing_evidence_jl_path, allow_stage3_global=True):
            print("self-test failed: Stage 3 Julia without evidence markers was accepted", file=sys.stderr)
            return 1
    print("self-test passed")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--derivation", type=Path, help="Markdown derivation to validate")
    parser.add_argument("--julia", type=Path, help="Generated Julia file to validate")
    parser.add_argument(
        "--allow-stage3-global",
        action="store_true",
        help="Allow explicitly opt-in BnB-PEP Stage 3/Gurobi patterns when evidence markers are present",
    )
    parser.add_argument("--self-test", action="store_true", help="Run static-linter self-test")
    args = parser.parse_args()

    if args.self_test:
        return self_test()

    if not args.derivation and not args.julia:
        parser.error("provide --derivation, --julia, or --self-test")

    errors: list[str] = []
    if args.derivation:
        errors.extend(validate_derivation(args.derivation))
    if args.julia:
        errors.extend(validate_julia(args.julia, allow_stage3_global=args.allow_stage3_global))

    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1
    print("static lint passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
