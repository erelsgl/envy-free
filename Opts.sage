#
# The Opts class represents a disjunction - several possible Dicts.
# 
# Author: Erel Segai-Halevi
# Date:   2015-10
#

# load ("/home/erelsgl/git/envy-free/Dict.sage")

def and_opts(opts1, opts2):
    """
        returns  a "cartesian product" of the given opts (which represent an AND operation).
    """
    the_new_opts = []
    for dict2 in opts2:
        the_new_opts += [and_dicts(dict1,dict2) for dict1 in opts1]
    return the_new_opts
    
def opts_explanations(opts):
    exps = []
    for dict in opts:
        if dict.has_key('?'):
            exps.append(dict['?'])
    return exps
    
def filter_opts(title, opts1, opts2, cycles=None):
    """
        Filter opts1 by:
            a. And-ing them with opts2
            b. Removing opts with contradictions (cycles)
        Returns the cycles in the "cycles" variable.
        Note: opts1 and cycles are modified!
        
        returns: opts1 after the filter.
    """
    opts3 = and_opts(opts1, opts2)
    del opts1[:]
    if cycles!=None:
        del cycles[:]
    for the_dict in opts3:
        the_dict_cycles = dict_cycles(the_dict)
        if the_dict_cycles:
           if cycles!=None:
               cycles.append(the_dict_cycles)
        else:
           opts1.append(the_dict)
    
    """ explanations """
    exps = ""
    spaces = len(title)*' '
    if opts1: 
        opts1_exps = opts_explanations(opts1)
        if opts1_exps:
            if len(opts1_exps)<=4:  # short explanations
                exps = ": " + (";  ".join(", ".join(map(str,l)) for l in opts1_exps))
            else:  # long explanations
                exps = ""
        cases_string = "case" if len(opts1)==1 else "cases"
        print title+" may fail in", len(opts1), cases_string, exps ,"."
    
    else:
        print title+" always succeeds."
    if cycles and len(opts1)==0:
       print spaces, "cycles: ", cycles
       
    return opts1
    
def Opts_examples():
   # EXAMPLE (expected: [ {'a':1<2 5<6}, {'a':5<6,'b': 3<4}, {'a':1<2,'b':7<8}, {'b':3<4 7<8}])
   print and_opts([ {'a':Pref([[1,2]])}, {'b':Pref([[3,4]])} ], [ {'a':Pref([[5,6]])}, {'b':Pref([[7,8]])} ])	 

   # EXAMPLE (expected: [ ], since this is AND with EMPTY)
   print and_opts([ {'a':Pref([[1,2]])}, {'b':Pref([[3,4]])} ], [  ])
  
   # EXAMPLE (expected: [{'a': 1<2, 'b': 3<4}])
   print and_opts([ {'a':Pref([[1,2]])}] , [{'b':Pref([[3,4]])} ])
   
   print opts_explanations([ {'a': Pref([ [1,2] ])}, {'a': Pref([ [3,4] ]),'?':['this is what A wants']} ])
 
 
   # EXAMPLE (expects " may fail in  3  cases : a wants 2, a wants 2;  a wants 4, a wants 2;  a wants 2, a wants 3 ."
   # [{'a': [[1, 2]]}, {'a': [[3, 4], [1, 2]]}, {'a': [[1, 2], [4, 3]]}])
   opts1 = [ {'a': Pref([ [1,2] ]), '?':['a wants 2'], '*':Pref([])}, {'a': Pref([ [3,4] ]), '?':['a wants 4'], '*':Pref([])} ]
   opts2 = [ {'a': Pref([ [1,2] ]), '?':['a wants 2'], '*':Pref([])}, {'a': Pref([ [4,3] ]), '?':['a wants 3'], '*':Pref([])} ]
   cycles = []
   filter_opts("test", opts1, opts2, cycles)
   print opts1
   print "cycles: ",cycles


# Used as return value to indicate that the required operation necessarily fails.
def must_fail(title, opts1, reason=None):
    message = " must fail"
    if reason:
        message += " because of "+reason+"."
    print title+message
    return opts1
