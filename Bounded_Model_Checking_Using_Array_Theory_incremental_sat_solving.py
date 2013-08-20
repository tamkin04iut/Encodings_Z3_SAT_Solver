from z3 import *
import random
import timeit
import datetime
import time


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
        #print "Constraint 1: Nodes index value constraints:"
        #for i in range(self.totalNodes):
          #print nodes_index_constraint[i]
        self.Z3solver.add(nodes_index_constraint)
        
    def add_start_end_node_index_constraint(self):
        #constraint 2: Start End constraints
        start_end_constraint = And( self.Nodes[0] == self.startNodeIndex, self.Nodes[self.totalNodes - 1] == self.endNodeIndex)
        #print "\nConstraint 2: Start-End node index constraints:"
        #print start_end_constraint
        self.Z3solver.add(start_end_constraint)
        
    def add_distinct_node_index_value_constraint(self):
        #constraint 3: Each Nodes value should be distinct
        nodes_index_distinct_constraint  = Distinct(self.Nodes)
        #print "\nConstraint 3: Each Nodes index value distinct constraints:"
        #print nodes_index_distinct_constraint
        self.Z3solver.add(nodes_index_distinct_constraint)
        
    def add_cost_bound_constraints(self, bound):
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

        bound_contraint = Sum(totalDistance) <= bound
        #print "\nConstraint 4: total distance bound constraints"
        #print bound_contraint
        self.Z3solver.add(bound_contraint)
        
    def add_constraints(self):
        
        self.add_node_index_value_constraint()
        self.add_start_end_node_index_constraint()
        self.add_distinct_node_index_value_constraint()
        
    def create_solver_instance(self):
        #Create the Solver
        self.Z3solver = Solver()        
    def create_nodes_as_int_sort(self):
        #Create Node as int sort variables like n_0, n_1 ...
        self.Nodes = [ Int("n_%s" % (i)) for i in range(self.totalNodes) ]
        #print "We have these nodes:"
        #for i in range(self.totalNodes):
            #print self.Nodes[i]
    
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
        #print "\nWe have these traveling cost matrix:"
        #print_matrix(self.TravelingTimeMatrix)


    def find_model_within_bound_incremental(self):
        #self.Z3solver.set(timeout=1000)
        while True:
            print "Incremental approach:"
            self.Z3solver.push()
            self.add_cost_bound_constraints(self.bound)
            #print self.Z3solver           
            start_time = time.time()
            print "\nFinding Model for %d nodes within bound %d." %(self.totalNodes, self.bound)
            print "----------------------------------------------"
            if self.Z3solver.check() == sat:
                end_time = time.time()
                print "SAT"
                print "Model: "
                m = self.Z3solver.model()
                nodeIndex = [ m.evaluate(self.Nodes[i]) for i in range(self.totalNodes) ]
                result = []
                result.append(nodeIndex)
                print_matrix(result)
                totalCost = 0
                print "Traversing costs: "
                for i in range(len(nodeIndex)-1):
                    node1Index = int(nodeIndex[i].as_string())
                    node2Index = int(nodeIndex[i+1].as_string())
                    cost = self.TravelingTimeMatrix[node1Index + 1][node2Index + 1]
                    print "%d -- %d : %d" % (node1Index , node2Index, cost) 
                    totalCost += cost
                print "Total cost: %d" % totalCost
                print "Bound: %d" % self.bound
                print "Execution time %s" % str(datetime.timedelta(seconds = end_time - start_time))
                self.Z3solver.pop()
                self.bound = self.bound - 50
                if self.bound == 0:
                    print "Exiting program..."
                    break
            elif result == unsat:
                print "UNSAT"
                print "No model found within bound %d" % (self.bound)    
            else:
                print "Couldn't find. Reason unknown"
                print "Failed to solve"
                
    def find_model_within_bound_non_incremental(self):
        while True:
            self.create_solver_instance()
            self.add_constraints()
            self.add_cost_bound_constraints(self.bound)            
            #print self.Z3solver
            #self.Z3solver.set("timeout", 30)
            start_time = time.time()
            print "\nFinding Model for %d nodes within bound %d." %(self.totalNodes, self.bound)
            print "----------------------------------------------"
            if self.Z3solver.check() == sat:
                end_time = time.time()
                print "SAT"
                print "Model: "
                m = self.Z3solver.model()
                nodeIndex = [ m.evaluate(self.Nodes[i]) for i in range(self.totalNodes) ]
                result = []
                result.append(nodeIndex)
                print_matrix(result)
                totalCost = 0
                print "Traversing costs: "
                for i in range(len(nodeIndex)-1):
                    node1Index = int(nodeIndex[i].as_string())
                    node2Index = int(nodeIndex[i+1].as_string())
                    cost = self.TravelingTimeMatrix[node1Index + 1][node2Index + 1]
                    print "%d -- %d : %d" % (node1Index , node2Index, cost) 
                    totalCost += cost
                print "Total cost: %d" % totalCost
                print "Bound: %d" % self.bound
                print "Execution time %s" % str(datetime.timedelta(seconds = end_time - start_time))
                self.bound = self.bound - 10
                if self.bound < 10:
                    print "Exiting program..."
                    break
            elif result == unsat:
                print "UNSAT"
                print "No model found within bound %d" % (self.bound)    
            else:
                print "Couldn't find. Reason unknown"
                print "Failed to solve"

            

# Main program
def runTest(bound):
    problem = Bounded_Model_Checking_Using_Array_Theory(bound,12,0,5)    
    #problem.find_model_within_bound_incremental()
    problem.find_model_within_bound_non_incremental()
    
if __name__ == '__main__':
    runTest(50)
    #timeInSec = timeit.timeit("runTest(%d)" % (300), 
                              #setup="from __main__ import runTest", 
                              #number = 1)
    #print "Took %s sec." % timeInSec
    #print "Took time : %s" % str(datetime.timedelta(seconds = timeInSec))