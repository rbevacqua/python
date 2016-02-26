#Look for #IMPLEMENT tags in this file. These tags indicate what has
#to be implemented.
from collections import deque
from copy import deepcopy

'''
This file will contain different constraint propagators to be used within
bt_search.

propagator == a function with the following template
    propagator(csp, newly_instantiated_variable=None)
        ==> returns (True/False, [(Variable, Value), (Variable, Value) ...])

    csp is a CSP object---the propagator can use this to get access to the
    variables and constraints of the problem. The assigned variables can be
    accessed via methods, the values assigned can also be accessed.

    newly_instaniated_variable is an optional argument.
    if newly_instantiated_variable is not None:
        then newly_instantiated_variable is the most
        recently assigned variable of the search.
    else:
        propagator is called before any assignments are made
        in which case it must decide what processing to do
        prior to any variables being assigned. SEE BELOW

    The propagator returns True/False and a list of (Variable, Value) pairs.

    Returns False if a deadend has been detected by the propagator.
        in this case bt_search will backtrack
    Returns True if we can continue.

    The list of variable values pairs are all of the values
    the propagator pruned (using the variable's prune_value method).
    bt_search NEEDS to know this in order to correctly restore these
    values when it undoes a variable assignment.

    NOTE propagator SHOULD NOT prune a value that has already been
    pruned! Nor should it prune a value twice

    PROPAGATOR called with newly_instantiated_variable = None
        PROCESSING REQUIRED:
            for plain backtracking (where we only check fully instantiated
            constraints) we do nothing...return (true, [])

            for forward checking (where we only check constraints with one
            remaining variable) we look for unary constraints of the csp
            (constraints whose scope contains only one variable) and we
            forward_check these constraints.

            for gac we establish initial GAC by initializing the GAC queue with
            all constaints of the csp

    PROPAGATOR called with newly_instantiated_variable = a variable V
        PROCESSING REQUIRED:
            for plain backtracking we check all constraints with V (see csp
            method get_cons_with_var) that are fully assigned.

            for forward checking we forward check all constraints with V that
            have one unassigned variable left

            for gac we initialize the GAC queue with all constraints containing
            V.
'''

def prop_BT(csp, newVar=None):
    '''Do plain backtracking propagation. That is, do no
    propagation at all. Just check fully instantiated constraints'''

    if not newVar:
        return True, []
    for c in csp.get_cons_with_var(newVar):
        if c.get_n_unasgn() == 0:
            vals = []
            vars = c.get_scope()
            for var in vars:
                vals.append(var.get_assigned_value())
            if not c.check(vals):
                return False, []
    return True, []

def prop_FC(csp, newVar=None):
    '''Do forward checking.  That is, check constraints with only one
    uninstantiated variable, and prune appropriately.  (i.e., do not prune a
    value that has already been pruned; do not prune the same value twice.)
    Return if a deadend has been detected, and return the variable/value pairs
    that have been pruned.  See beginning of this file for complete description
    of what propagator functions should take as input and return.

    Input: csp, (optional) newVar.
        csp is a CSP object---the propagator uses this to
        access the variables and constraints.

        newVar is an optional argument.
        if newVar is not None:
            then newVar is the most recently assigned variable of the search.
            run FC on all constraints that contain newVar.
        else:
            propagator is called before any assignments are made in which case
            it must decide what processing to do prior to any variable
            assignment.

    Returns: (boolean,list) tuple, where list is a list of tuples:
             (True/False, [(Variable, Value), (Variable, Value), ... ])

        boolean is False if a deadend has been detected, and True otherwise.

        list is a set of variable/value pairs that are all of the values the
        propagator pruned.
    '''

    if not newVar:
        cons = csp.get_all_cons()
    else:
        cons = csp.get_cons_with_var(newVar)

    pruned = []
    for c in cons:
        if c.get_n_unasgn() == 1:
            vars = c.get_scope()
            for var in vars:

                # get unassigned var and it's cur_domain
                if not var.is_assigned():
                    curDom = var.cur_domain()
                    unassigned_var = var

            for val in curDom:
                vals = []
                unassigned_var.assign(val)

                for var in vars:
                        vals.append(var.get_assigned_value())

                if not c.check(vals):

                    if unassigned_var.in_cur_domain(val):
                        unassigned_var.prune_value(val)
                        pruned.append((unassigned_var, val))

                    if unassigned_var.cur_domain_size == 0:
                        unassigned_var.unassign()
                        return False, pruned

                unassigned_var.unassign()

    return True, pruned





#IMPLEMENT

def prop_GAC(csp, newVar=None):
    '''Do GAC propagation, as described in lecture. See beginning of this file
    for complete description of what propagator functions should take as input
    and return.

    Input: csp, (optional) newVar.
        csp is a CSP object---the propagator uses this to access the variables
        and constraints.

        newVar is an optional argument.
        if newVar is not None:
            do GAC enforce with constraints containing newVar on the GAC queue.
        else:
            Do initial GAC enforce, processing all constraints.

    Returns: (boolean,list) tuple, where list is a list of tuples:
             (True/False, [(Variable, Value), (Variable, Value), ... ])

    boolean is False if a deadend has been detected, and True otherwise.

    list is a set of variable/value pairs that are all of the values the
    propagator pruned.
    '''

    pruned = []
    if not newVar:
        cons = deque(csp.get_all_cons())
    else:
        cons = deque(csp.get_cons_with_var(newVar))

        #prune all vals not equal to the val of newVar in cur_domain of newVar
        new_curDom = newVar.cur_domain()
        for val in new_curDom:
            if val != newVar.get_assigned_value():
                newVar.prune_value(val)
                pruned.append((newVar, val))

    
    while len(cons) != 0:
        c = cons.popleft()
        vars = c.get_scope()
        for var in vars:
            for val in var.cur_domain():
                # check if an assignment is found
                if not c.has_support(var, val):
                    
                    #remove val from cur_domain of var
                    if var.in_cur_domain(val):
                        var.prune_value(val)
                        pruned.append((var, val))

                    if var.cur_domain_size() == 0:
                        return False, pruned

                    else:
                        # add constraints that contain var that are also not in the queue, 
                        # since we just pruned it's domain
                        for c2 in csp.get_cons_with_var(var):
                            if c2 not in cons:
                                cons.append(c2)

    return True, pruned


#Helper for GAC
'''return a boolean value True if it finds an assignment with var=val, otherwise False, this algorithm is recursive'''
def find_assignments(ass, var, val, variables, constraint, num, l):
    
    if l == num:
        return constraint.check(ass)
        
    v = variables[num]

    if v == var:
        ass.append(val)

        res = find_assignments(ass, var, val, variables, constraint, num+1, l)

        ass.pop()

        return res

    else:
        for value in v.cur_domain():
            ass.append(value)
            res = find_assignments(ass, var, val, variables, constraint,num+1,l)
            if res:
                return res
            ass.pop()

        return res