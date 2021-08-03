import re
from sympy.parsing.latex import parse_latex
import sympy as sp

# import sys


class Fact:
    def __init__(self, name, params):
        self.name = name
        if type(params) == list:
            self.params = params
        elif type(params) == str:
            self.params = [s.strip() for s in params.split(",")]
        else:
            raise ValueError(f"Invalid params = {params}")

        # Convert to expression whenever required
        for idx, param in enumerate(self.params):
            if isinstance(param, str) and not re.fullmatch("[a-zA-Z_]+", param):
                # savedStdout = sys.stdout
                # sys.stdout = None  # close the stdout to mute the warning information
                try:
                    self.params[idx] = parse_latex(param)
                    # sys.stdout = savedStdout
                except Exception as e:
                    # sys.stdout = savedStdout
                    raise e

    def compare(self, target, param_map=None):
        if param_map is None:
            param_map = {}
        local_param_map = dict(param_map)
        if self.__compare(target, local_param_map):
            param_map.update(local_param_map)
            return True
        else:
            return False

    def __compare(self, target, param_map):
        if self.name == target.name and len(self.params) == len(target.params):
            matched = []
            for idx, param in enumerate(self.params):
                param_matched = False
                if type(param) == type(target.params[idx]):  # noqa
                    if type(param) == str:
                        param_img = (
                            param
                            if param[:1].islower()
                            else param_map.get(param, target.params[idx])
                        )
                        if param_img == target.params[idx]:
                            param_matched = True

                        if param not in param_map:
                            param_map[param] = param_img

                    elif type(param) == Fact:
                        param_matched = param.__compare(target.params[idx], param_map)

                    elif isinstance(param, sp.Expr):
                        param_matched = param.equals(target.params[idx])

                    else:
                        raise ValueError(
                            f"unknown parameter type : {type(param)}, value = {param}"
                        )

                matched.append(param_matched)

            return all(matched)

        return False

    def map_instance(self, p_map):
        params = []
        for param in self.params:
            if type(param) == str:
                if re.fullmatch("[a-zA-Z_]+", param):
                    if param[:1].islower():
                        params.append(param)
                    else:
                        if param in p_map:
                            params.append(p_map[param])
                        else:
                            raise ValueError(
                                f"parameter map missing value for key = {param}"
                            )
                else:
                    expr = parse_latex(param)
                    params.append(expr.subs(p_map))
            elif type(param) == Fact:
                params.append(param.map_instance(p_map))

        return Fact(self.name, params)

    def __repr__(self):
        param_str = ", ".join([str(p) for p in self.params])
        return f"{self.name}({param_str})"


class Rule:
    def __init__(self, clausses, implications):
        self.clausses = clausses
        self.implications = implications

    def __repr__(self):
        cl = ", ".join([str(c) for c in self.clausses])
        df = ", ".join([str(d) for d in self.implications])
        return f"{cl} => {df}"


def parse_facts(state, predicate_set=None):

    if predicate_set is None:
        predicate_set = set()

    start_idx = 0
    params = []
    fact = None
    idx = 0
    while idx < len(state):
        s = state[idx]
        if s == "(":
            sub_params, skip = parse_facts(state[idx + 1 :], predicate_set)  # noqa
            fact = Fact(state[start_idx:idx].strip(), sub_params)
            predicate_set.add(fact.name)
            idx += skip + 1
            start_idx = idx + 1
        elif s == ",":
            if fact:
                params.append(fact)
                fact = None
            else:
                params.append(state[start_idx:idx].strip())
            start_idx = idx + 1
        elif s == ")":
            if fact:
                params.append(fact)
                fact = None
            else:
                params.append(state[start_idx:idx].strip())
            return params, idx

        idx += 1

    if fact:
        params.append(fact)

    return params


def parse_rules(state, predicate_set=None):
    if predicate_set is None:
        predicate_set = set()

    match = re.fullmatch("([0-9a-zA-Z_ \(\),;]+)=>([0-9a-zA-Z_ \(\),;+-]+)", state)
    if match:
        groups = match.groups()
        implications = parse_facts(groups[1].strip(), predicate_set)
        rules = []
        for clausses_str in groups[0].split(";"):
            clausses = parse_facts(clausses_str.strip(), predicate_set)
            if len(clausses) > 0:
                rules.append(Rule(clausses, implications))
        return rules
    else:
        raise ValueError("Rule string doesn't match rule pattern")


class System:
    def __init__(self, definition=None, rules=None):
        definition = definition or []
        self.definition = []
        self.predicates = set()

        for defn in definition:
            if isinstance(defn, str):
                [self.add_fact(f) for f in parse_facts(defn, self.predicates)]
            elif isinstance(defn, Fact):
                self.add_fact(defn)
            else:
                ValueError(f"Invalid fact value = {defn}")

        rules = rules or []
        self.rules = []
        for rule in rules:
            if isinstance(rule, str):
                self.rules.extend(parse_rules(rule, self.predicates))
            elif isinstance(rule, Rule):
                self.rules.append(rule)
            else:
                ValueError(f"Invalid rule value = {rule}")

        self.solve_forward()

    def query(self, clausses, param_map=None):
        param_map = param_map or {}
        if len(clausses) == 0:
            yield [], param_map
        else:
            for fact in self.definition:
                local_param_map = dict(param_map)
                if clausses[0].compare(fact, local_param_map):
                    for fact_set, p_map in self.query(clausses[1:], local_param_map):
                        yield [fact] + fact_set, p_map

    def add_fact(self, fact):
        if not any([fact.compare(f) for f in self.definition]):
            self.definition.append(fact)

    def apply_rule(self, rule):
        new_facts = []
        for fact_set, p_map in self.query(rule.clausses):
            for imp in rule.implications:
                new_facts.append(imp.map_instance(p_map))

        return new_facts

    def apply_rules(self, rules):
        new_facts = []
        for rule in rules:
            new_facts.extend(self.apply_rule(rule))

        len_0 = len(self.definition)

        for fact in new_facts:
            self.add_fact(fact)

        len_1 = len(self.definition)
        return len_1 - len_0

    def solve_forward(self, max_steps=100):
        for _ in range(max_steps):
            added = self.apply_rules(self.rules)
            if not added:
                break

    def parse(self, state):
        # Is it a rule?
        match = re.search("([0-9a-zA-Z_ \(\),;]+)=>([0-9a-zA-Z_ \(\),;]+)", state)
        if match:
            groups = match.groups()
            implications = parse_facts(groups[1].strip(), self.predicates)
            for clausses_str in groups[0].split(";"):
                clausses = parse_facts(clausses_str.strip(), self.predicates)
                rule = Rule(clausses, implications)
                print(f"Rule: {rule}")
                self.rules.append(rule)
        # then it is a fact
        else:
            facts = parse_facts(state, self.predicates)
            for fact in facts:
                print(f"Fact: {fact}")
                self.add_fact(fact)

    def __repr__(self):
        return "\n".join(
            sorted([str(f) for f in self.definition])
            + [""]
            + sorted([str(r) for r in self.rules])
        )

