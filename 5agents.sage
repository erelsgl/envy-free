#
# This files generates a proof for the correctness of 
#      the following envy-free cake-cutting protocol for four agents:
#
# A:Equalize(4) 
# One of:
#    B:Equalize(2) C:Equalize(2)
#    B:Equalize(3) C:Equalize(2)
#    C:Equalize(2) B:Equalize(2)
#    C:Equalize(3) B:Equalize(2)
#

load ("4agents.sage")

def filter_by_equalize2_failure_5pieces(space, dict, cutter, observers, cycles):
    return filter_by_equalize2_failure_4pieces(space, dict, cutter, observers, cycles)

def filter_by_equalize3_failure_5pieces(space, dict, cutter, observers, cycles):
    """
        In Equalize(3), the cutter cuts his two best pieces (e.g, "5" becomes "5bb" and "4" becomes "4bb"),
           and equalizes it to his third best piece (e.g. "5bb" and "4bb" and "3" become best).
        If this fails, it means that BOTH observers prefer (5bb or 4bb), OR BOTH observers prefer (1 or 2), OR at least ONE observer prefers 3.
    """
    
    title = space+cutter+":Equalize(3)"
    the_opts = []   # a disjunction (OR) of possible preferences.

    whole_pieces = dict[cutter].chain;
    trimmed_pieces = list(whole_pieces);  trimmed_pieces[-1]+=cutter+cutter;   trimmed_pieces[-2]+=cutter+cutter; 
    monotonicity_prefs = [ [trimmed_pieces[-1], whole_pieces[-1]+cutter] ,
                           [trimmed_pieces[-2], whole_pieces[-2]       ] ]
    whole_pieces_before_trimming = whole_pieces[-2:]
    trimmed_pieces_after_trimming = trimmed_pieces[-2:]

    dict[cutter].equalities.append(trimmed_pieces[-3:])
    dict[cutter].calc_poset()
    dict['*'].inequalities += monotonicity_prefs + dict[cutter].global_cover_relations(trimmed_pieces_after_trimming)

    observer0_pref = dict[observers[0]]
    observer1_pref = dict[observers[1]]
    for i in [3,4]:
        for j in [3,4]:
            if i!=j:
                if observer0_pref.may_be_best(whole_pieces[i],whole_pieces_before_trimming) and \
                   observer1_pref.may_be_best(whole_pieces[j],whole_pieces_before_trimming): 
                     the_opts.append({
                       '?': [observers[0]+" wants "+trimmed_pieces[i]+" and "+observers[1]+" wants "+trimmed_pieces[j]],
                       observers[0]: Pref(Pref.by_best_piece(trimmed_pieces, i)),
                       observers[1]: Pref(Pref.by_best_piece(trimmed_pieces, j)),
                       })
    for i in [0,1]:
        for j in [0,1]:
            if i!=j:
                if observer0_pref.is_best(whole_pieces[i]) and \
                   observer1_pref.is_best(whole_pieces[j]):    
                     return must_fail(title, [dict], observers)       # since these two pieces are not cut
                if observer0_pref.may_be_best(whole_pieces[i],whole_pieces_before_trimming) and \
                   observer1_pref.may_be_best(whole_pieces[j],whole_pieces_before_trimming): 
                     the_opts.append({
                       '?': [observers[0]+" wants "+trimmed_pieces[i]+" and "+observers[1]+" wants "+trimmed_pieces[j]],
                       observers[0]: Pref(Pref.by_best_piece(trimmed_pieces, i)),
                       observers[1]: Pref(Pref.by_best_piece(trimmed_pieces, j)),
                       })

    for observer in observers: # We fail if one of the agents wants the middle piece (that was not cut)
        if dict[observer].is_best(whole_pieces[2]):  
            return must_fail(title, [dict], observer)       # since this piece is not cut
        if dict[observer].may_be_best(whole_pieces[2], whole_pieces_before_trimming):
            the_opts.append(dict_implied_by_best_piece({}, observer, trimmed_pieces, 2))
            
    return filter_opts(title, [dict], the_opts, cycles)


def filter_by_equalize4_failure_5pieces(space, dict, cutter, observers, cycles):
    """
        In Equalize(4), the cutter cuts his three best pieces (e.g, "5" becomes "5bbb" and "4" becomes "4bbb" and "3" becomes "3bbb"),
           and equalizes it to his fourth best piece (e.g. "3bbb" and "4bbb" and "3bbb" and "2" become best).
        If this fails, it means that ONE of the observers prefers either 1 or 2 over the other pieces.
    """

    title = space+cutter+":Equalize(4)"
    the_opts = []   # a disjunction (OR) of possible preferences.
    
    whole_pieces = dict[cutter].chain;
    trimmed_pieces = list(whole_pieces);
    trimmed_pieces[-1]+=cutter+cutter+cutter;   
    trimmed_pieces[-2]+=cutter+cutter+cutter;
    trimmed_pieces[-3]+=cutter+cutter+cutter; 
    monotonicity_prefs = [ [trimmed_pieces[-1], whole_pieces[-1]+cutter+cutter] ,
                           [trimmed_pieces[-2], whole_pieces[-2]+cutter+cutter] ,
                           [trimmed_pieces[-3], whole_pieces[-3]]               ]
    whole_pieces_before_trimming = whole_pieces[-3:]
    trimmed_pieces_after_trimming = trimmed_pieces[-3:]
    
    dict[cutter].equalities.append(trimmed_pieces[-4:])
    dict[cutter].calc_poset()
    dict['*'].inequalities += monotonicity_prefs + dict[cutter].global_cover_relations(trimmed_pieces_after_trimming)

    for observer in observers:
        observer_pref = dict[observer]
        for i in [0,1]:
            if observer_pref.is_best(whole_pieces[i]):            
                return must_fail(title, [dict], observer)  # since these pieces are not cut
            if observer_pref.may_be_best(whole_pieces[i], whole_pieces_before_trimming):
                the_opts.append(dict_implied_by_best_piece({}, observer, trimmed_pieces, i))

    return filter_opts(title, [dict], the_opts, cycles)        


def prove_5pieces_for_given_orders(b_order, c_order, d_order):
    dict_0 = {'b': Pref(chain=b_order), 'c':Pref(chain=c_order), 'd':Pref(chain=d_order), '*':Pref([]), '?':[]}
    opts_1 = filter_by_equalize2_failure_5pieces(" "*4, dict_0, cutter="b",observers="cd",cycles=None)
    if not opts_1: return None
    for index_1,dict_1 in enumerate(opts_1):    
        print " "*5+"CASE ",index_1," of ",len(opts_1),": ",dict_1['?'], ":"
        opts_2 = filter_by_equalize3_failure_5pieces(" "*6, dict_1, cutter="b",observers="cd",cycles=[])
        if not opts_2: continue
        for index_2,dict_2 in enumerate(opts_2):
            print " "*7+"case ",index_2," of ",len(opts_2),": ",dict_2['?'], ":"            
            opts_3 = filter_by_equalize4_failure_5pieces(" "*8, dict_2, cutter="b",observers="cd",cycles=[])
            if not opts_3: continue
            for index_3,dict_3 in enumerate(opts_3):
                print " "*9+"case ",index_3," of ",len(opts_3),": ",dict_3['?'], ":"
                opts_4 = filter_by_equalize2_failure_5pieces(" "*10, dict_3, cutter="c",observers="db",cycles=[])
                if not opts_4: continue
                for index_4,dict_4 in enumerate(opts_4):
                    print " "*11+"CASE ",index_4," of ",len(opts_4),": ",dict_4['?'], ":"
                    opts_5 = filter_by_equalize3_failure_5pieces(" "*12, dict_4, cutter="c",observers="db",cycles=[])
                    if not opts_5: continue
                    for index_5,dict_5 in enumerate(opts_5):
                        print " "*13+"case ",index_5," of ",len(opts_5),": ",dict_5['?'], ":"                        
                        opts_6 = filter_by_equalize4_failure_5pieces(" "*14, dict_5, cutter="c",observers="dd",cycles=[])
                        if not opts_6: continue
                        for index_6,dict_6 in enumerate(opts_6):
                            print " "*15+"case ",index_6," of ",len(opts_6),": ",dict_6['?'], ":"
                            opts_7 = filter_by_equalize2_failure_5pieces(" "*16, dict_6, cutter="d",observers="bc",cycles=[])
                            if not opts_7: continue
                            for index_7,dict_7 in enumerate(opts_7):
                                print " "*17+"CASE ",index_7," of ",len(opts_7),": ",dict_7['?'], ":"
                                opts_8 = filter_by_equalize3_failure_5pieces(" "*18, dict_7, cutter="d",observers="bc",cycles=[])
                                if not opts_8: continue
                                for index_8,dict_8 in enumerate(opts_8):
                                    print " "*19+"case ",index_8," of ",len(opts_8),": ",dict_8['?'], ":"
                                    opts_9 = filter_by_equalize4_failure_5pieces(" "*20, dict_8, cutter="d",observers="bc",cycles=[])
                                    if not opts_9: continue
                                    
                                    print "\n\n*** Failure! "
                                    return opts_9
 

def prove_5pieces_for_given_order_sets(b_orders, c_orders, d_orders):
    t = cputime()
    for b_order in b_orders:
        for c_order in c_orders:
            for d_order in d_orders:
                print "Consider the case in which the orderings are: b:", Pref.repr_chain(b_order), "  c:", Pref.repr_chain(c_order), "    d:", Pref.repr_chain(d_order)
                opts = prove_5pieces_for_given_orders(b_order, c_order, d_order)

                if opts:
                    print "\n\nThe claim is not proved! It is false, for example, in the following case:\n", opts[0]
                    return
    print "\nQ.E.D! (", cputime(t), " sec)"


def disprove_5pieces():
    a_pieces = ["1","2","3","4","5"]
    print "Initially, agent a cuts five equal pieces: ", ",".join(a_pieces),"."
    
    prove_5pieces_for_given_order_sets(
        [["1","2","3","4","5"]], # preference order of B: 1<2<3<4<5
        [["1","2","3","4","5"]], # preference order of C: 1<2<3<4<5
        [["5","4","3","2","1"], ["1","3","2","4","5"]]) # preference orders of D: 5<4<3<2<1 (easy); 1<3<2<4<5 (fails).
        #[["1","2","3","4","5"], ["5","4","3","2","1"], ["1","3","2","4","5"]]) # Possible preference orders of D: 1<2<3<4<5, 5<4<3<2<1, 1<3<2<4<5

print "5 agents functions loaded! You can run 'disprove_5pieces()'"
