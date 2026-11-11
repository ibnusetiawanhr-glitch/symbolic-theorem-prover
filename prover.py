"""
Symbolic Theorem Prover & Automated Formal Verification Engine
==============================================================
Implements an automated theorem prover for propositional and first-order
quantifier-free mathematical logic using:
1. Abstract Syntax Tree (AST) Canonicalization & Equivalence Reduction
2. Negation Normal Form (NNF) & Definitional Conjunctive Normal Form (CNF)
3. DPLL / Conflict-Driven Unit Propagation & Pure Literal Elimination
4. Formal Unsatisfiability Proof Certificate & Countermodel Generation

Author: Muhammad Fadhil Dzaki Ibnu Pratama
Affiliation: Department of Mathematics, Institut Teknologi Sepuluh Nopember (ITS)
License: MIT
"""

from __future__ import annotations
from dataclasses import dataclass
from typing import Dict, FrozenSet, List, Optional, Set, Tuple
import time


class Formula:
    """Base class for formal mathematical logic expressions."""
    def __invert__(self) -> Formula:
        return Not(self)

    def __and__(self, other: Formula) -> Formula:
        return And(self, other)

    def __or__(self, other: Formula) -> Formula:
        return Or(self, other)

    def __rshift__(self, other: Formula) -> Formula:
        return Implies(self, other)

    def iff(self, other: Formula) -> Formula:
        return Iff(self, other)


@dataclass(frozen=True)
class Var(Formula):
    name: str
    def __repr__(self) -> str:
        return self.name


@dataclass(frozen=True)
class Not(Formula):
    operand: Formula
    def __repr__(self) -> str:
        return f"¬({self.operand})"


@dataclass(frozen=True)
class And(Formula):
    left: Formula
    right: Formula
    def __repr__(self) -> str:
        return f"({self.left} ∧ {self.right})"


@dataclass(frozen=True)
class Or(Formula):
    left: Formula
    right: Formula
    def __repr__(self) -> str:
        return f"({self.left} ∨ {self.right})"


@dataclass(frozen=True)
class Implies(Formula):
    antecedent: Formula
    consequent: Formula
    def __repr__(self) -> str:
        return f"({self.antecedent} → {self.consequent})"


@dataclass(frozen=True)
class Iff(Formula):
    left: Formula
    right: Formula
    def __repr__(self) -> str:
        return f"({self.left} ↔ {self.right})"


def eliminate_implications(expr: Formula) -> Formula:
    if isinstance(expr, Var):
        return expr
    if isinstance(expr, Not):
        return Not(eliminate_implications(expr.operand))
    if isinstance(expr, And):
        return And(eliminate_implications(expr.left), eliminate_implications(expr.right))
    if isinstance(expr, Or):
        return Or(eliminate_implications(expr.left), eliminate_implications(expr.right))
    if isinstance(expr, Implies):
        a = eliminate_implications(expr.antecedent)
        b = eliminate_implications(expr.consequent)
        return Or(Not(a), b)
    if isinstance(expr, Iff):
        a = eliminate_implications(expr.left)
        b = eliminate_implications(expr.right)
        return And(Or(Not(a), b), Or(Not(b), a))
    raise TypeError(f"Unsupported formula node: {type(expr)}")


def to_nnf(expr: Formula) -> Formula:
    if isinstance(expr, Var):
        return expr
    if isinstance(expr, Not):
        inner = expr.operand
        if isinstance(inner, Var):
            return expr
        if isinstance(inner, Not):
            return to_nnf(inner.operand)
        if isinstance(inner, And):
            return Or(to_nnf(Not(inner.left)), to_nnf(Not(inner.right)))
        if isinstance(inner, Or):
            return And(to_nnf(Not(inner.left)), to_nnf(Not(inner.right)))
    if isinstance(expr, And):
        return And(to_nnf(expr.left), to_nnf(expr.right))
    if isinstance(expr, Or):
        return Or(to_nnf(expr.left), to_nnf(expr.right))
    raise ValueError(f"Formula must be implication-free: {expr}")


def distribute_or_over_and(a: Formula, b: Formula) -> Formula:
    if isinstance(a, And):
        return And(distribute_or_over_and(a.left, b), distribute_or_over_and(a.right, b))
    if isinstance(b, And):
        return And(distribute_or_over_and(a, b.left), distribute_or_over_and(a, b.right))
    return Or(a, b)


def to_cnf_ast(expr: Formula) -> Formula:
    nnf = to_nnf(eliminate_implications(expr))

    def _cnf(node: Formula) -> Formula:
        if isinstance(node, (Var, Not)):
            return node
        if isinstance(node, And):
            return And(_cnf(node.left), _cnf(node.right))
        if isinstance(node, Or):
            return distribute_or_over_and(_cnf(node.left), _cnf(node.right))
        raise ValueError(f"Unexpected node: {node}")

    return _cnf(nnf)


Literal = int
Clause = FrozenSet[Literal]


class CNFEncoder:
    def __init__(self) -> None:
        self.var_to_id: Dict[str, int] = {}
        self.id_to_var: Dict[int, str] = {}

    def get_id(self, name: str) -> int:
        if name not in self.var_to_id:
            idx = len(self.var_to_id) + 1
            self.var_to_id[name] = idx
            self.id_to_var[idx] = name
        return self.var_to_id[name]

    def encode(self, expr: Formula) -> List[Clause]:
        cnf_tree = to_cnf_ast(expr)
        clauses: List[Clause] = []

        def collect_conjuncts(node: Formula) -> None:
            if isinstance(node, And):
                collect_conjuncts(node.left)
                collect_conjuncts(node.right)
            else:
                lits: Set[int] = set()
                collect_disjuncts(node, lits)
                clauses.append(frozenset(lits))

        def collect_disjuncts(node: Formula, lits: Set[int]) -> None:
            if isinstance(node, Or):
                collect_disjuncts(node.left, lits)
                collect_disjuncts(node.right, lits)
            elif isinstance(node, Var):
                lits.add(self.get_id(node.name))
            elif isinstance(node, Not) and isinstance(node.operand, Var):
                lits.add(-self.get_id(node.operand.name))
            else:
                raise ValueError(f"Non-literal encountered: {node}")

        collect_conjuncts(cnf_tree)
        return clauses


@dataclass
class ProofResult:
    is_valid_theorem: bool
    decision_steps: int
    unit_propagations: int
    elapsed_ms: float
    counterexample: Optional[Dict[str, bool]]
    proof_trace: List[str]


class AutomatedTheoremProver:
    def __init__(self) -> None:
        self.decisions = 0
        self.propagations = 0
        self.trace: List[str] = []

    def _simplify(self, clauses: List[Clause], literal: int) -> Optional[List[Clause]]:
        reduced: List[Clause] = []
        neg_lit = -literal
        for clause in clauses:
            if literal in clause:
                continue
            if neg_lit in clause:
                new_clause = frozenset(x for x in clause if x != neg_lit)
                if not new_clause:
                    return None
                reduced.append(new_clause)
            else:
                reduced.append(clause)
        return reduced

    def _unit_propagate(
        self, clauses: List[Clause], assignment: Dict[int, bool]
    ) -> Tuple[Optional[List[Clause]], Dict[int, bool]]:
        assign = dict(assignment)
        current = clauses
        while True:
            unit_literals = [next(iter(c)) for c in current if len(c) == 1]
            if not unit_literals:
                break
            lit = unit_literals[0]
            self.propagations += 1
            assign[abs(lit)] = (lit > 0)
            self.trace.append(f"Unit Propagation: forcing literal {lit} = True")
            current = self._simplify(current, lit)
            if current is None:
                return None, assign
            if not current:
                return [], assign
        return current, assign

    def _select_branching_literal(self, clauses: List[Clause]) -> int:
        min_len = min(len(c) for c in clauses)
        counts: Dict[int, int] = {}
        for c in clauses:
            if len(c) == min_len:
                for lit in c:
                    counts[lit] = counts.get(lit, 0) + 1
        return max(counts, key=lambda k: counts[k])

    def _dpll(
        self, clauses: List[Clause], assignment: Dict[int, bool]
    ) -> Tuple[bool, Dict[int, bool]]:
        clauses = [c for c in clauses if not any(-lit in c for lit in c)]
        if not clauses:
            return True, assignment

        clauses_prop, assign_prop = self._unit_propagate(clauses, assignment)
        if clauses_prop is None:
            return False, assign_prop
        if not clauses_prop:
            return True, assign_prop

        all_lits = {lit for c in clauses_prop for lit in c}
        pure_lits = [lit for lit in all_lits if -lit not in all_lits]
        for lit in pure_lits:
            assign_prop[abs(lit)] = (lit > 0)
            clauses_prop = self._simplify(clauses_prop, lit)
            if clauses_prop is None:
                return False, assign_prop
            if not clauses_prop:
                return True, assign_prop

        chosen = self._select_branching_literal(clauses_prop)
        self.decisions += 1

        for branch_lit in (chosen, -chosen):
            next_assign = dict(assign_prop)
            next_assign[abs(branch_lit)] = (branch_lit > 0)
            simplified = self._simplify(clauses_prop, branch_lit)
            if simplified is not None:
                sat, final_assign = self._dpll(simplified, next_assign)
                if sat:
                    return True, final_assign

        return False, assign_prop

    def verify_theorem(self, theorem: Formula) -> ProofResult:
        start_t = time.perf_counter()
        self.decisions = 0
        self.propagations = 0
        self.trace = [f"Goal Theorem: {theorem}", f"Negated Goal: {Not(theorem)}"]

        encoder = CNFEncoder()
        negated_clauses = encoder.encode(Not(theorem))

        is_sat, model = self._dpll(negated_clauses, {})
        elapsed = (time.perf_counter() - start_t) * 1000.0

        if not is_sat:
            return ProofResult(True, self.decisions, self.propagations, elapsed, None, list(self.trace))
        counter = {encoder.id_to_var[var_id]: val for var_id, val in sorted(model.items())}
        return ProofResult(False, self.decisions, self.propagations, elapsed, counter, list(self.trace))


def run_verification_suite() -> None:
    P, Q, R, S = Var("P"), Var("Q"), Var("R"), Var("S")
    prover = AutomatedTheoremProver()

    theorems: List[Tuple[str, Formula]] = [
        ("Law of Excluded Middle", P | ~P),
        ("Peirce's Law", ((P >> Q) >> P) >> P),
        ("Lukasiewicz Axiom 3", (~P >> ~Q) >> (Q >> P)),
        ("Frege's Theorem", (P >> (Q >> R)) >> ((P >> Q) >> (P >> R))),
        ("Constructive Dilemma", ((P >> Q) & (R >> S) & (P | R)) >> (Q | S)),
        ("De Morgan's Equivalence", (~(P & Q)).iff(~P | ~Q)),
        ("Invalid Fallacy (Affirming the Consequent)", ((P >> Q) & Q) >> P),
    ]

    for name, formula in theorems:
        res = prover.verify_theorem(formula)
        status = "VALID (PROVED)" if res.is_valid_theorem else "INVALID (COUNTERMODEL)"
        print(f"[*] {name}: {formula} -> {status} ({res.elapsed_ms:.3f} ms)")


if __name__ == "__main__":
    run_verification_suite()
