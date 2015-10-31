#
# The Dict class represents Prefs of different agents.
#     It is like a dictionary that matches the agent's letter to its Pref.
# 
# A Dict contains a key for every agent: 'b','c','d'... and two special keys:
#    '?': text explanation;
#    '*': relations that are true for ALL agents.
#
# Author: Erel Segai-Halevi
# Date:   2015-10
#

# load ("/home/erelsgl/git/envy-free/Pref.sage")


def and_dicts(dict1, dict2):
    """
       returns an elementwise-concatenation of the given dictionaries (which represents an AND operation).
    """
    new_dict = {}
    for agent,pref in dict1.iteritems():
        new_dict[agent] = copy(pref)
    for agent,pref in dict2.iteritems():
        #print agent,pref
        if new_dict.has_key(agent):
            if agent=='?':
                new_dict[agent] += pref
            else:
                if isinstance(new_dict[agent],list):
                    raise AttributeError("new_dict["+agent+"] is list! "+str(new_dict[agent]))
                new_dict[agent].and_with(pref)
        else:
            new_dict[agent] = copy(pref)
    return new_dict
    
def dict_to_posets(dict, debug=None):
    """
        dict is a dictionary of prefs.
        The returned value is a dictionary of posets.
    """
    the_dict_of_posets = {}
    global_pref = dict['*']
    for agent,pref in dict.iteritems():
        if agent!='?' and agent!='*':
            the_dict_of_posets[agent] = pref.calc_poset(global_pref)
    return the_dict_of_posets
    
def dict_cycles(dict):
    """ returns a dict with the cycles in each pref in this dict (if any) """
    the_dict_of_cycles = {}
    global_pref = dict['*']
    for agent,pref in dict.iteritems():
        if agent!='?' and agent!='*':
            cyc = pref.cycle(global_pref)
            if cyc:
                the_dict_of_cycles[agent] = Pref.repr_chain(cyc)
    
    if the_dict_of_cycles and dict.has_key('?'):
       the_dict_of_cycles['?'] = ", ".join(dict['?'])  # keep the explanations

    return the_dict_of_cycles


def dict_implied_by_best_piece(base_dict, agent, pieces, best_piece_index):
    base_dict['?'] = [agent+" wants "+pieces[best_piece_index]]
    base_dict[agent] = Pref(inequalities=Pref.by_best_piece(pieces,best_piece_index))
    return base_dict
    
def dict_explanation(dict):
	if dict.has_key('?'):
		return "Assume the case   " + dict['?'][-1] + ". Then:"
	else:
		return ""

def Dict_examples():
    # EXAMPLE (expected: {'?': ['dict1', 'dict2'], 'a': 1<2 5<6, 'b': 3<4, 'c': 7<8})
    print and_dicts({'a':Pref([[1,2]]), 'b':Pref([[3,4]]), '?': ['dict1']}, 
          {'a':Pref([[5,6]]), 'c':Pref([[7,8]]), '?': ['dict2']})	
          
    # EXAMPLE (expected: {'a': 1<2, 'b': 3<4})
    print and_dicts({'a':Pref([[1,2]]), 'b':Pref([[3,4]])}, {'b': Pref([])})
 
    # EXAMPLE (expected: {'a': Finite poset containing 6 elements, 'b': Finite poset containing 4 elements})
    print dict_to_posets({'a':Pref([[1,2],[3,4]]), 'b':Pref([[1,2]]), '*':Pref([[5,6]])})
    
    # EXAMPLE (expected: ValueError: The graph is not directed acyclic)
    #print dict_to_posets({'a':Pref([[1,2],[3,4]]), 'b':Pref([[1,2]]), '*':Pref([[2,1]])})
    
    # EXAMPLE (expects: {'?': ['cycle test'], 'b': [1, 2, 1]})
    print dict_cycles({'a':Pref([[2,1],[3,4]]), 'b':Pref([[1,2]]), '*':Pref([[2,1]]), '?': ["cycle test"]})    
    
    # EXAMPLE
    print dict_implied_by_best_piece({'*':[]}, "b", ["1","2","3"], -1)
    
