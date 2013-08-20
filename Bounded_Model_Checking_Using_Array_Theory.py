from z3 import *
import random
import timeit
import datetime


class Bounded_Model_Checking_Using_Array_Theory:    
    
    def __init__(self, bound, totalNodes, startNodeIndex, endNodeIndex):
        self.bound = bound
        self.totalNodes = totalNodes
        self.startNodeIndex = startNodeIndex
        self.endNodeIndex = endNodeIndex
        self.create_nodes_as_int_sort()
        self.create_cost_matrix()
        self.create_solver_instance()
        self.add_constraints()
    
    def get_node_index_value_constraint(self,i):
          if(i != 0 and i != self.totalNodes - 1):
            return And(self.Nodes[i] >= 0, self.Nodes[i] < self.totalNodes)
          else:
            return True
    def add_node_index_value_constraint(self):
        # constraint 1: Nodes index must be 0 <= and  <= totalNodes
        nodes_index_constraint  = [ self.get_node_index_value_constraint(i) for i in range(self.totalNodes)]
        print "Constraint 1: Nodes index value constraints:"
        for i in range(self.totalNodes):
          print nodes_index_constraint[i]
        self.Z3solver.add(nodes_index_constraint)
        
    def add_start_end_node_index_constraint(self):
        #constraint 2: Start End constraints
        start_end_constraint = And( self.Nodes[0] == self.startNodeIndex, self.Nodes[self.totalNodes - 1] == self.endNodeIndex)
        print "\nConstraint 2: Start-End node index constraints:"
        print start_end_constraint
        self.Z3solver.add(start_end_constraint)
        
    def add_distinct_node_index_value_constraint(self):
        #constraint 3: Each Nodes value should be distinct
        nodes_index_distinct_constraint  = Distinct(self.Nodes)
        print "\nConstraint 3: Each Nodes index value distinct constraints:"
        print nodes_index_distinct_constraint
        self.Z3solver.add(nodes_index_distinct_constraint)
        
    def add_cost_bound_constraints(self): 

        #constraint 4: distance(n_0, n_1) + ... distance(n_n-1, n_n) <= Bound
        I = IntSort()
        D = Array('D', I, I)
        for i in range(1, self.totalNodes + 1):
          for j in range(1, self.totalNodes + 1):
            k = (i-1) * self.totalNodes + (j-1)
            self.Z3solver.add(D == Store(D, k, self.TravelingTimeMatrix[i][j]))

        totalDistance  = []
        for i in range(self.totalNodes - 1):
          totalDistance.append(D[self.Nodes[i] * self.totalNodes + self.Nodes[i+ 1]])

        bound_contraint = Sum(totalDistance) <= self.bound
        print "\nConstraint 4: total distance bound constraints"
        print bound_contraint
        self.Z3solver.add(bound_contraint)
        
    def add_constraints(self):
        
        self.add_node_index_value_constraint()
        self.add_start_end_node_index_constraint()
        self.add_distinct_node_index_value_constraint()
        self.add_cost_bound_constraints()
        
    def create_solver_instance(self):
        #Create the Solver
        self.Z3solver = Solver()        
    def create_nodes_as_int_sort(self):
        #Create Node as int sort variables like n_0, n_1 ...
        self.Nodes = [ Int("n_%s" % (i)) for i in range(self.totalNodes) ]
        print "We have these nodes:"
        for i in range(self.totalNodes):
            print self.Nodes[i]
    
    def get_random_cost_value(self,i,j):
          if(i==0 and j == 0):
            return "."
          if(i == 0):
           return j-1
          elif(j==0):
            return i-1
          else:
            return random.randint(1,20)

    def create_cost_matrix(self):
        #Create a random traveling cost matrix
        self.TravelingTimeMatrix = [ [ self.get_random_cost_value(i,j) for i in range(self.totalNodes + 1) ]
                                                                for j in range(self.totalNodes + 1) ]
        print "\nWe have these traveling cost matrix:"
        print_matrix(self.TravelingTimeMatrix)

    
    def find_model_within_bound(self):
        print "\nResult:"
        print "-----------------------------------"
        if self.Z3solver.check() == sat:
            print "SAT"
            print "Model: "
            m = self.Z3solver.model()
            nodeIndex = [ m.evaluate(self.Nodes[i]) for i in range(self.totalNodes) ]
            result = []
            result.append(nodeIndex)

            print_matrix(result)
            totalCost = 0
            for i in range(len(nodeIndex)-1):
                node1Index = int(nodeIndex[i].as_string())
                node2Index = int(nodeIndex[i+1].as_string())
                cost = self.TravelingTimeMatrix[node1Index + 1][node2Index + 1]
                print "%d -- %d : %d" % (node1Index , node2Index, cost) 
                totalCost += cost
            print "Total cost: %d" % totalCost
            print "Bound: %d" % self.bound
            
        else:
            print "UNSAT"
            print "failed to solve"



# Main program
def runTest():
    problem = Bounded_Model_Checking_Using_Array_Theory(500,15,0,9)
    problem.find_model_within_bound()
    
if __name__ == '__main__':
    timeInSec = timeit.timeit("runTest()", 
                              setup="from __main__ import runTest", 
                              number = 1)
    #print "Took %s sec." % timeInSec
    print "Took time : %s" % str(datetime.timedelta(seconds = timeInSec))