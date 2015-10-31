#
# This files generates a proof for the correctness of 
#      the following envy-free cake-cutting protocol for four agents:
#
# A:Equalize(4) 
# One of:
#    B:Equalize(2)
#    B:Equalize(3)
#    C:Equalize(2)
#    C:Equalize(3)
#

def filter_by_equalize2_failure_4pieces(space, dict, cutter, observers, cycles):
    """
        space:     a string of spaces for display purposes.
        dict:      a dictionary matching agents (letters) to Prefs.
        cutter:    a lower-case letter representing the cutting agent, e.g. "b".
        observers: a string representing the other agents, e.g. "c" or "cd".
        cycles:    a location to put the cycles, if found.
        
        In Equalize(2), the cutter cuts his best piece (e.g, "4" becomes "4b"),
            and equalizes it to his second best piece (e.g. "4b" and "3" become best).
        If this fails, it means that the other agent prefers either "4b" or "3" over the other pieces.        
    """

    title = space+cutter+":Equalize(2)"
    the_opts = []   # a disjunction (OR) of possible preferences.
    
    whole_pieces = dict[cutter].chain;
    trimmed_pieces = list(whole_pieces);  trimmed_pieces[-1]+=cutter
    monotonicity_prefs = [ [trimmed_pieces[-1], whole_pieces[-1]] ]
    whole_pieces_before_trimming = whole_pieces[-1:]
    trimmed_pieces_after_trimming = trimmed_pieces[-1:]

    dict[cutter].equalities.append(trimmed_pieces[-2:])
    dict[cutter].calc_poset()
    dict['*'].inequalities += monotonicity_prefs + dict[cutter].global_cover_relations(trimmed_pieces_after_trimming)

    for observer in observers:
        observer_pref = dict[observer]
        if observer_pref.is_best(whole_pieces[-2]):
           return must_fail(title, [dict], observer) # since piece -2 is not cut
        for i in [-1,-2]:
            if observer_pref.may_be_best(whole_pieces[i], whole_pieces_before_trimming):
                the_opts.append(dict_implied_by_best_piece({}, observer, trimmed_pieces, i))
    return filter_opts(title, [dict], the_opts, cycles)
    
    
def filter_by_equalize3_failure_4pieces(space, dict, cutter, observers, cycles):
    """
        space:     a string of spaces for display purposes.
        dict:      a dictionary matching agents (letters) to Prefs.
        cutter:    a lower-case letter representing the cutting agent, e.g. "b".
        observers: a string representing the other agents, e.g. "c" or "cd".
        cycles:    a location to put the cycles, if found.
        
        In Equalize(3), the cutter cuts his two best pieces (e.g, "4" becomes "4bb" and "3" becomes "3bb"),
            and equalizes it to his third best piece (e.g. "4bb", "3bb" and "2" become best).
        If this fails, it means that the other agent prefers either "2" or "1" over the other pieces.
    """

    title = space+cutter+":Equalize(3)"
    the_opts = []

    whole_pieces = dict[cutter].chain;
    trimmed_pieces = list(whole_pieces);  trimmed_pieces[-1]+=cutter+cutter;   trimmed_pieces[-2]+=cutter+cutter; 
    floor_piece = whole_pieces[-3]
    monotonicity_prefs = [ [trimmed_pieces[-1], whole_pieces[-1]+cutter] ,
                           [trimmed_pieces[-2], whole_pieces[-2]       ] ]
    whole_pieces_before_trimming = whole_pieces[-2:]
    trimmed_pieces_after_trimming = trimmed_pieces[-2:]

    dict[cutter].equalities.append(trimmed_pieces[-3:])
    dict[cutter].calc_poset()
    dict['*'].inequalities += monotonicity_prefs + dict[cutter].global_cover_relations(trimmed_pieces_after_trimming)
    
    for observer in observers:
        observer_pref = dict[observer]
        for i in [0,1]:        
            if observer_pref.is_best(whole_pieces[i]):
               return must_fail(title, [dict], observer) # since these two pieces are not cut
            if observer_pref.may_be_best(whole_pieces[i], whole_pieces_before_trimming):
               the_opts.append(dict_implied_by_best_piece({}, observer, trimmed_pieces, i))
    return filter_opts(title, [dict], the_opts, cycles)
    
def prove_4pieces_for_given_orders(b_order, c_order):
    dict_0 = {'b': Pref(chain=b_order), 'c':Pref(chain=c_order), '*':Pref()}

    opts_1 = filter_by_equalize2_failure_4pieces(" "*2, dict_0, cutter="b",observers="c",cycles=None)
    if not opts_1: return None

    for dict_1 in opts_1:
        print " "*2, dict_explanation(dict_1)
        opts_2 = filter_by_equalize3_failure_4pieces(" "*4, dict_1, cutter="b",observers="c",cycles=None)
        if not opts_2: continue
        
        for dict_2 in opts_2:
            print " "*4,  dict_explanation(dict_2)
            opts_3 = filter_by_equalize2_failure_4pieces(" "*6, dict_2, cutter="c",observers="b", cycles=None)
            if not opts_3: continue
            
            for dict_3 in opts_3:
                print " "*6,  dict_explanation(dict_3)
                opts_4 = filter_by_equalize3_failure_4pieces(" "*8, dict_3, cutter="c",observers="b", cycles=None)
                if not opts_4: continue

                print "Failure!"
                print dict_3
                print opts_4
                raise Exception("Not proved!")

def prove_4pieces():
    a_pieces = ["1","2","3","4"]
    print "Initially, agent a cuts four equal pieces: ", ",".join(a_pieces),"."
    
    b_orders = [a_pieces]
    c_orders = Poset([a_pieces,[]]).linear_extensions()
    num_of_c_orders = len(c_orders)
    
    print "Consider the following",num_of_c_orders,"cases regarding the preferences of b and c:"
    
    for b_order in b_orders: 
        for index_c,c_order in enumerate(c_orders):
            print "\nCASE",(index_c+1),"OF",num_of_c_orders, \
                  ": b's order is", Pref.repr_chain(b_order), \
                  "and c's order is", Pref.repr_chain(c_order),":"
            
            prove_4pieces_for_given_orders(b_order, c_order)
    print "\nQ.E.D!"
