import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact])
        ####################################################
        # Student code goes here
        def rule_remove(rule,kb):
            if rule.name=='rule':
                for existing_rule in kb.rules:
                    if rule==existing_rule and existing_rule.supported_by==[]:
                        for supported_fact in existing_rule.supports_facts:
                            for fact_rule_pair in supported_fact.supported_by:
                                if fact_rule_pair[1]==rule:
                                    supported_fact.supported_by.remove(fact_rule_pair)
                                    if (supported_fact.supported_by==[]
                                        and not supported_fact.asserted):
                                        print('KILLING',supported_fact)
                                        self.kb_retract(supported_fact)
                        for supported_rule in existing_rule.supports_rules:
                            for fact_rule_pair in supported_rule.supported_by:
                                if fact_rule_pair[1]==rule:
                                    supported_rule.supported_by.remove(fact_rule_pair)
                                    if (supported_fact.supported_by==[]
                                        and not supported_fact.asserted):
                                        print('KILLING',supported_rule)
                                        rule_remove(supported_rule,self)
                        self.rules.remove(existing_rule)
            
            


        
        if fact.name=='fact':
            for existing_fact in self.facts:
                if fact==existing_fact and existing_fact.supported_by==[]:
                    for supported_fact in existing_fact.supports_facts:
                        for fact_rule_pair in supported_fact.supported_by:
                            if fact_rule_pair[0]==fact:
                                supported_fact.supported_by.remove(fact_rule_pair)
                                if (supported_fact.supported_by==[]
                                    and not supported_fact.asserted):
                                    print('KILLING',supported_fact)
                                    self.kb_retract(supported_fact)
                    for supported_rule in existing_fact.supports_rules:
                        for fact_rule_pair in supported_rule.supported_by:
                            if fact_rule_pair[0]==fact:
                                supported_rule.supported_by.remove(fact_rule_pair)
                                if (supported_rule.supported_by==[]
                                    and not supported_rule.asserted):
                                    print('KILLING',supported_rule)
                                    rule_remove(supported_rule,self)
                    self.facts.remove(existing_fact)
                        

class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing            
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here
        for condition in rule.lhs:
            bindings = match(fact.statement,condition)
            if bindings:
                #breakpoint()
                new_conditions=rule.lhs.copy()
                if new_conditions[0]==condition:
                    new_conditions=new_conditions[1:]
                    if new_conditions==[]:
                        new_statement=instantiate(rule.rhs,bindings)
                        new_fact=Fact(new_statement,[[fact,rule]])
                        fact.supports_facts.append(new_fact)
                        rule.supports_facts.append(new_fact)
                        kb.kb_add(new_fact)
                    else:
                        lhs=[]
                        rhs=instantiate(rule.rhs,bindings)
                        for new_condition in new_conditions:
                            new_statement=instantiate(new_condition,bindings)
                            lhs.append(new_statement)
                        new_rule=Rule([lhs,rhs],[[fact,rule]])
                        fact.supports_rules.append(new_rule)
                        rule.supports_rules.append(new_rule)
                        kb.kb_add(new_rule)
