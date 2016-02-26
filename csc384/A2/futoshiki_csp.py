#Look for #IMPLEMENT tags in this file. These tags indicate what has
#to be implemented.

'''
Construct and return Futoshiki CSP models.
'''

from cspbase import *
import itertools

def futoshiki_csp_model_1(initial_futoshiki_board):
    '''Return a CSP object representing a Futoshiki CSP problem along with an
    array of variables for the problem. That is return

    futoshiki_csp, variable_array

    where futoshiki_csp is a csp representing futoshiki using model_1 and
    variable_array is a list of lists

    [ [  ]
      [  ]
      .
      .
      .
      [  ] ]

    such that variable_array[i][j] is the Variable (object) that you built to
    represent the value to be placed in cell i,j of the futoshiki board
    (indexed from (0,0) to (n-1,n-1))


    The input board is specified as a list of n lists. Each of the n lists
    represents a row of the board. If a 0 is in the list it represents an empty
    cell. Otherwise if a number between 1--n is in the list then this
    represents a pre-set board position.

    Each list is of length 2n-1, with each space on the board being separated
    by the potential inequality constraints. '>' denotes that the previous
    space must be bigger than the next space; '<' denotes that the previous
    space must be smaller than the next; '.' denotes that there is no
    inequality constraint.

    E.g., the board

    -------------------
    | > |2| |9| | |6| |
    | |4| | | |1| | |8|
    | |7| <4|2| | | |3|
    |5| | | | | |3| | |
    | | |1| |6| |5| | |
    | | <3| | | | | |6|
    |1| | | |5|7| |4| |
    |6> | |9| < | |2| |
    | |2| | |8| <1| | |
    -------------------
    would be represented by the list of lists

    [[0,'>',0,'.',2,'.',0,'.',9,'.',0,'.',0,'.',6,'.',0],
     [0,'.',4,'.',0,'.',0,'.',0,'.',1,'.',0,'.',0,'.',8],
     [0,'.',7,'.',0,'<',4,'.',2,'.',0,'.',0,'.',0,'.',3],
     [5,'.',0,'.',0,'.',0,'.',0,'.',0,'.',3,'.',0,'.',0],
     [0,'.',0,'.',1,'.',0,'.',6,'.',0,'.',5,'.',0,'.',0],
     [0,'.',0,'<',3,'.',0,'.',0,'.',0,'.',0,'.',0,'.',6],
     [1,'.',0,'.',0,'.',0,'.',5,'.',7,'.',0,'.',4,'.',0],
     [6,'>',0,'.',0,'.',9,'.',0,'<',0,'.',0,'.',2,'.',0],
     [0,'.',2,'.',0,'.',0,'.',8,'.',0,'<',1,'.',0,'.',0]]


    This routine returns Model_1 which consists of a variable for each cell of
    the board, with domain equal to [1,...,n] if the board has a 0 at that
    position, and domain equal [i] if the board has a fixed number i at that
    cell.

    Model_1 also contains BINARY CONSTRAINTS OF NOT-EQUAL between all relevant
    variables (e.g., all pairs of variables in the same row, etc.).

    All of the constraints of Model_1 MUST BE binary constraints (i.e.,
    constraints whose scope includes two and only two variables).
    '''

    #Create Variable Objects
    vars = []
    var_array = []
    inequality_array = []
    num_rows = len(initial_futoshiki_board)

    if num_rows > 0:
      num_cols = len(initial_futoshiki_board[0])

    #domain if Variable is 0 initially
    dom = []
    for i in range(num_rows):
      dom.append(i+1)

    for i in range(num_rows):
      row = []
      row_inequality = []
      for j in range(num_cols):
        if j % 2 == 0:
          if initial_futoshiki_board[i][j] == 0: 
            var = Variable("V{}{}".format(i, j//2), dom)
          else: # cell has fixed value
            fixed = []
            fixed.append(initial_futoshiki_board[i][j])
            var = Variable("V{}{}".format(i, j//2), fixed)

          row.append(var)
          vars.append(var)

        else:
          row_inequality.append(initial_futoshiki_board[i][j])


      inequality_array.append(row_inequality)
      var_array.append(row)

    # Create Constraint objects for the model
    cons = []
    n = len(var_array)
    
    for i in range(n):
      for j in range(n):
        for x in range(j+1, n):
          #row constraints
          var1 = var_array[i][j]
          var2 = var_array[i][x]
          con = Constraint("C(V{}{},V{}{})".format(i,j,i,x), [var1, var2])
          sat_tuples = []
          for t in itertools.product(var1.cur_domain(),var2.cur_domain()):
            if checker(inequality_array[i][j], (i, j), (i, x), t[0], t[1]):
              sat_tuples.append(t)

          con.add_satisfying_tuples(sat_tuples)
          cons.append(con)

          # column constraints

          var1 = var_array[j][i]
          var2 = var_array[x][i]
          con = Constraint("C(V{}{},V{}{})".format(j,i,x,i), [var1, var2])
          sat_tuples = []
          for t in itertools.product(var1.cur_domain(), var2.cur_domain()):
            if checker('.', (j,i), (x,i), t[0], t[1]):
              sat_tuples.append(t)

          con.add_satisfying_tuples(sat_tuples)
          cons.append(con)

    csp = CSP("{}x{}-futoshiki".format(n,n), vars)

    for c in cons:
      csp.add_constraint(c)

    return csp, var_array




##############################

def futoshiki_csp_model_2(initial_futoshiki_board):
    '''Return a CSP object representing a futoshiki CSP problem along with an
    array of variables for the problem. That is return

    futoshiki_csp, variable_array

    where futoshiki_csp is a csp representing futoshiki using model_2 and
    variable_array is a list of lists

    [ [  ]
      [  ]
      .
      .
      .
      [  ] ]

    such that variable_array[i][j] is the Variable (object) that you built to
    represent the value to be placed in cell i,j of the futoshiki board
    (indexed from (0,0) to (n-1,n-1))

    The input board takes the same input format (a list of n lists of size 2n-1
    specifying the board) as futoshiki_csp_model_1.

    The variables of Model_2 are the same as for Model_1: a variable for each
    cell of the board, with domain equal to [1,...,n] if the board has a 0 at
    that position, and domain equal [n] if the board has a fixed number i at
    that cell.

    However, Model_2 has different constraints. In particular, instead of
    binary non-equals constaints Model_2 has 2*n all-different constraints:
    all-different constraints for the variables in each of the n rows, and n
    columns. Each of these constraints is over n-variables (some of these
    variables will have a single value in their domain). Model_2 should create
    these all-different constraints between the relevant variables, and then
    separately generate the appropriate binary inequality constraints as
    required by the board. There should be j of these constraints, where j is
    the number of inequality symbols found on the board.  
    '''

    #Create Variable Objects
    vars = []
    var_array = []
    inequality_array = []
    num_rows = len(initial_futoshiki_board)

    if num_rows > 0:
      num_cols = len(initial_futoshiki_board[0])

    #domain if Variable is 0 initially
    dom = []
    for i in range(num_rows):
      dom.append(i+1)

    for i in range(num_rows):
      row = []
      row_inequality = []
      for j in range(num_cols):
        if j % 2 == 0:
          if initial_futoshiki_board[i][j] == 0: 
            var = Variable("V{}{}".format(i, j//2), dom)
          else: # cell has fixed value
            fixed = []
            fixed.append(initial_futoshiki_board[i][j])
            var = Variable("V{}{}".format(i, j//2), fixed)

          row.append(var)
          vars.append(var)

        else:
          row_inequality.append(initial_futoshiki_board[i][j])


      inequality_array.append(row_inequality)
      var_array.append(row)

    # Create Constraint objects for the model
    cons = []
    n = len(var_array)

    #rows
    for i in range(n):
      row_vars = list(var_array[i])
      col_vars = []
      col_var_doms = []
      row_var_doms = []
      for j in range(n):
        # get domains of all vars in the same row 
        row_var_doms.append(var_array[i][j].cur_domain())

        # collect colunm vars and there respective domains
        col_vars.append(var_array[j][i])
        col_var_doms.append(var_array[j][i].cur_domain())

        #create binary inequality constraints
        if j < len(inequality_array[i]):
          var1 = var_array[i][j]
          var2 = var_array[i][j+1]

          # if statement is used in order to create binary constraints
          # between variables that have an inequality 
          if inequality_array[i][j] != '.':
            con = Constraint("C(V{}{},V{}{})".format(i,j,i,j+1), [var1, var2])
            sat_tuples = []
            for t in itertools.product(var1.cur_domain(), var2.cur_domain()):
              if inequality_checker(inequality_array[i][j], t[0], t[1]):
                sat_tuples.append(t)

            con.add_satisfying_tuples(sat_tuples)
            cons.append(con)



      # create all-diff row constraint
      con = Constraint("C(Row-{})".format(i), row_vars)
      sat_tuples = []
      for t in itertools.product(*row_var_doms):
        if all_diff_checker(row_vars, t):
          sat_tuples.append(t)
          
      con.add_satisfying_tuples(sat_tuples)
      cons.append(con)

      # create all-diff column constraints
      con = Constraint("C(Col-{})".format(i), col_vars)
      sat_tuples = []
      for t in itertools.product(*col_var_doms):
        if all_diff_checker(col_vars, t):
          sat_tuples.append(t)

      con.add_satisfying_tuples(sat_tuples)
      cons.append(con)

    csp = CSP("{}x{}-futoshiki".format(n,n), vars)

    for c in cons:
      csp.add_constraint(c)

    return csp, var_array



def checker(inequality, var1_tup, var2_tup, val1, val2):
  result = val1 != val2

  # check if var1 and var2 are adjacent cells
  if var1_tup[1] + 1 == var2_tup[1]:
    result = result and inequality_checker(inequality,val1,val2)

  return result

def inequality_checker(inequality, val1, val2):
  result = True

  if inequality == '<':
    result = (val1 < val2)

  elif inequality == '>':
    result = (val1 > val2)

  return result

def all_diff_checker(vars, vals):
  result = True
  for i in range(len(vars)):
    for j in range(i+1, len(vars)):
      result = result and (vals[i] != vals[j])

  return result


