
from z3 import *
import random
import timeit
import datetime
import time

def get_random_cost_value(i,j):
    return random.randint(1,20)

def create_cost_matrix(totalNodes):
    TravelingTimeMatrix = [ [ get_random_cost_value(i,j) for i in range(totalNodes) ]
                                                            for j in range(totalNodes) ]
    print "\nWe have these traveling cost matrix:"
    rows = []
    for i in range(totalNodes + 1 ):
        row =[i]
        for j in range(totalNodes + 1):
            if(j == 0):
                continue
            elif(i >=1 and j >= 1):
                row.append(TravelingTimeMatrix[i-1][j-1])
            else:
                row.append(j)
                
        rows.append(row)
    print_matrix(rows)
    return TravelingTimeMatrix
    #print_matrix(TravelingTimeMatrix)
    
    
    
def get_node_index_value_constraint(i, nodes, totalNodes):
    return And(nodes[i] >= 0, nodes[i] < totalNodes)
        
def node_index_value_constraint(nodes):
    totalNodes = len(nodes)
    nodes_index_constraint  = [ get_node_index_value_constraint(i,nodes, totalNodes) for i in range(totalNodes)]
    return nodes_index_constraint
        
def start_end_node_index_constraint(nodes, startNodeIndex, endNodeIndex ):
    totalNodes = len(nodes)
    start_end_constraint = And( nodes[0] == startNodeIndex, nodes[totalNodes - 1] == endNodeIndex)
    return start_end_constraint

def distinct_node_index_value_constraint(nodes):
    nodes_index_distinct_constraint  = Distinct(nodes)
    return nodes_index_distinct_constraint

if __name__ == '__main__':
    s = Solver()
    totalNodes = 40
    startNodeIndex = 0
    endNodeIndex = 3
    bound = 150
    
    costMatrix = create_cost_matrix(totalNodes)
    nodes = [ Int("n_%s" % (i)) for i in range(totalNodes) ]
    nodes_index_constraint = node_index_value_constraint(nodes)
    s.add(nodes_index_constraint)
    start_end_constraint = start_end_node_index_constraint(nodes, startNodeIndex, endNodeIndex)
    s.add(start_end_constraint)
    nodes_index_distinct_constraint = distinct_node_index_value_constraint(nodes)
    s.add(nodes_index_distinct_constraint)
    
    f = Function('f', IntSort(), IntSort(),IntSort())
    costs  = []
    for i in range(totalNodes):
        for j in range(totalNodes):
            costs.append(f(i,j) == costMatrix[i][j])
    costs_constraint = And(costs)
    s.add(costs_constraint)
    
    totalDistance  = []
    for i in range(totalNodes - 1):
      totalDistance.append(f(nodes[i], nodes[i+1]))
    bound_constraint = Sum(totalDistance) <= bound
    s.add(bound_constraint)
    print s
    start_time = time.time()
    if s.check() == sat:
        end_time = time.time()
        print "sat"
        m = s.model()
        nodeIndex = [ m.evaluate(nodes[i]) for i in range(totalNodes) ]
        print nodeIndex
        totalCost = 0
        for i in range(len(nodeIndex)-1):
            node1Index = int(nodeIndex[i].as_string())
            node2Index = int(nodeIndex[i+1].as_string())
            cost = costMatrix[node1Index][node2Index]
            print "%d -- %d : %d" % (node1Index , node2Index, cost) 
            totalCost += cost
        print "Total cost: %d" % totalCost
        print "Bound: %d" % bound
        print "Execution time %s" % str(datetime.timedelta(seconds = end_time - start_time))
    else:
        print "unsat"
    '''
    c1 = And(f(1,1) == 1, f(1,2) == 1, f(1,3) == 1,
             f(2,1) == 1, f(2,2) == 1, f(2,3) == 1,
             f(3,1) == 1, f(3,2) == 1, f(3,3) == 1)
    c2 = And(x >= 1, x <= 3)
    c3 = And(y >= 1, y <= 3)
    c4 = And(z >= 1, z <= 3)
    c5 = Distinct(x,y,z)
    c6 = f(x,y) + f(y,z) <= 2
    s.add(c1 , c2 , c3 , c4, c5, c6)

    #s.add(c1,f(1,1)+ f(1,2) < 4)
    if s.check() == sat:
      m = s.model()
      g = m.evaluate(c6)
      print g
      print m
    else:
      print "unsat"
    '''
    

