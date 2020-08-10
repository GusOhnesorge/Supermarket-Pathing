from tkinter import *
import heapq
from collections import defaultdict
import time

## Adjacency Matrix has a row for each node and each row has a columns for
## each node.
## 0 means no adjacent node and 1 means yes adjacent node
class AdjacencyMatrix():
    def __init__(self, total_nodes):
        self.matrix = [[9999 for col in range(total_nodes)] for row in range(total_nodes)]
        self.paths = [[-1 for col in range(total_nodes)] for row in range(total_nodes)]

    def getCell(self, row, column):
        return self.matrix[row][column]

    def setCell(self, row, column, value):
        self.matrix[row][column] = value

    def getPathCell(self, row, column):
        return self.paths[row][column]

    def setPathCell(self, row, column, value):
        self.paths[row][column] = value

    def pathList(self, id1, id2):
        path = []
        while self.paths[id1][id2] != id1:
            path.insert(0, self.paths[id1][id2])
            id2 = self.paths[id1][id2]
        return path #returns a pathlist of cell id's

class Edge():
    def __init__(self, first_node, second_node, distance):
        self.node1 = first_node
        self.node2 = second_node
        self.distance = distance
        self.neighbors = []
        self.color = "white"

    def __repr__(self):
        first = str(self.node1)
        second = str(self.node2)
        return "{0} : {1} , {2}".format(first, second, str(self.distance))
    def __str__(self):
        first = str(self.node1)
        second = str(self.node2)
        return "{0} : {1} , {2}".format(first, second, str(self.distance))

    def __key(self):
        return (first_node, second_node, distance)

    def __eq__(self, other):
        if isinstance(other, Edge):
            if self.node1 == other.node1:
                if self.node2 == other.node2:
                    return True
            if self.node2 == other.node1:
                if self.node1 == other.node2:
                    return True
            return False

class Graph:
    def __init__(self,edges):
        self.V = edges #No. of edges
        self.graph = defaultdict(list) # default dictionary to store graph


    # function to add an edge to graph
    def addEdge(self,v,w):
        self.graph[v].append(w) #Add w to v_s list
        self.graph[w].append(v) #Add v to w_s list

    def isCyclicUtil(self,v,visited,parent):

        #Mark the current node as visited
        visited[v] = True

        #Recur for all the edges adjacent to this edge
        for i in self.graph[v]:
            # If the node is not visited then recurse on it
            if  visited[i]==False :
                if(self.isCyclicUtil(i,visited,v)):
                    return True
            # If an adjacent edge is visited and not parent of current edge,
            # then there is a cycle
            elif  parent!=i:
                return True

        return False


    #Returns true if the graph contains a cycle, else false.
    def isCyclic(self):
        # Mark all the edges as not visited
        visited =[False]*(self.V)
        # Call the recursive helper function to detect cycle in different
        #DFS trees
        for i in range(self.V):
            if visited[i] == False: #Don't recur for u if it is already visited
                if (self.isCyclicUtil(i,visited,-1)) == True:
                    return True

        return False

class Node():
#A node class for A* Pathfinding
    def __init__(self, parent=None, position=None):
        self.parent = parent
        self.position = position
        self.g = 0
        self.h = 0
        self.f = 0
        self.adjacents = []

    def addAdjacent(self, new_node):
        self.adjacents.append(new_node)

    def __key(self):
        return self.position

    def __hash__(self):
        return hash(self.__key())

    def __repr__(self):
         (x, y) = self.position
         return "({0}, {1})".format(x, y)

    def __str__(self):
        (x, y) = self.position
        return "({0}, {1})".format(x, y)

    def __eq__(self, other):
        if isinstance(other, Node):
            return self.__key() == other.__key()

        return NotImplemented

    def __ne__(self, other):
        return not self.__eq__(other)

    def __lt__(self, other):
        return self.position < other.position

    def __le__(self, other):
        return self.position <= other.position

    def __gt__(self, other):
        return self.position > other.position

class Cell():
    FILLED_COLOR = "white"
    COLOR_BORDER = "black"

    def __init__(self, master, x, y, id, size):
        """ Constructor of the object called by Cell(...) """
        self.master = master
        self.id = id
        self.x = x
        self.y = y
        self.position = (x, y)
        self.size = size

    def _switch(self):
        """ Switch if the cell is filled or not. """
        self.FILLED_COLOR = self.master.cur_color_
        self.COLOR_BORDER = self.master.cur_color_

    def draw(self):
        """ order to the cell to draw its representation on the canvas """
        if self.master != None :
            if self.master.is_eraser:
                self.FILLED_COLOR = "white"
                self.COLOR_BORDER = "black"
            fill = self.FILLED_COLOR
            outline = self.COLOR_BORDER

            xmin = self.x * self.size
            xmax = xmin + self.size
            ymin = self.y * self.size
            ymax = ymin + self.size

            self.master.create_rectangle(xmin, ymin, xmax, ymax, fill = fill, outline = outline)

    def getColor(self):
        return self.FILLED_COLOR

    def __repr__(self):
         (x, y) = self.position
         return "({0}, {1})".format(x, y)

    def __str__(self):
        (x, y) = self.position
        return "({0}, {1})".format(x, y)

    def __key(self):
        return self.position

    def __eq__(self, other):
        if isinstance(other, Cell):
            return self.__key() == other.__key()
        return NotImplemented

class CellGrid(Canvas):

    def __init__(self, master, rowNumber, columnNumber, cellSize, *args, **kwargs):
        Canvas.__init__(self, master, width = cellSize * columnNumber , height = cellSize * rowNumber, *args, **kwargs)

        self.cellSize = cellSize
        self.rows = rowNumber
        self.columns = columnNumber
        self.grid = []
        self.cur_color_ = "black"
        self.is_eraser = False
        self.adjList = None
        self.adjMatrix = None
        #dest_cells and astarpaths have the same number of indices, hence why
        #you can use them to get info about the other
        self.dest_cells = []
        self.astarpaths = []
        id = 0
        for row in range(rowNumber):
            line = []
            for column in range(columnNumber):
                line.append(Cell(self, column, row, id, cellSize))
                id+=1

            self.grid.append(line)

        #memorize the cells that have been modified to avoid many switching of state during mouse motion.
        self.switched = []

        #bind click action
        self.bind("<Button-1>", self.handleMouseClick)
        #bind moving while clicking
        self.bind("<B1-Motion>", self.handleMouseMotion)
        #bind release button action - clear the memory of midified cells.
        self.bind("<ButtonRelease-1>", lambda event: self.switched.clear())

        self.draw()

        #Fills dest_cells to be used with Astar for all pairs pathing
    def fillDestinations(self):
        new_dests = []
        rows = self.rows
        columns = self.columns
        for row in range(rows):
            for column in range(columns):
                if self.grid[row][column].FILLED_COLOR == "red":
                    new_dests.append(self.grid[row][column])
                elif self.grid[row][column].FILLED_COLOR == "green":
                    new_dests.insert(0, self.grid[row][column])
        self.dest_cells = new_dests

    def draw(self):
        for row in self.grid:
            for cell in row:
                cell.draw()

    def _eventCoords(self, event):
        row = int(event.y / self.cellSize)
        column = int(event.x / self.cellSize)
        return row, column

    def handleMouseClick(self, event):
        row, column = self._eventCoords(event)
        cell = self.grid[row][column]
        cell._switch()
        cell.draw()
        #add the cell to the list of cell switched during the click
        self.switched.append(cell)

    def handleMouseMotion(self, event):
        row, column = self._eventCoords(event)
        cell = self.grid[row][column]

        if cell not in self.switched:
            cell._switch()
            cell.draw()
            self.switched.append(cell)

    def makePathCell(self, coords):
        (x, y) = coords
        save_color = self.cur_color_
        self.cur_color_ = "blue"
        cell = self.grid[y][x]
        cell._switch()
        cell.draw()
        #add the cell to the list of cell switched during the click
        self.cur_color_ = save_color

    def save():
       print("Saved")

    def onEraser(self):
        self.is_eraser = True

    def offEraser(self):
        self.is_eraser = False

    def onPen(self):
        self.offEraser()

    def makeShelfColor(self):
        self.cur_color_ = "black"

    def makeListItemColor(self):
        self.cur_color_  = "red"

    def makeEntranceColor(self):
        self.cur_color_  = "green"

    def makeMatrix(self):
        print("Timing Making Adjacency Matrix")
        time_start = time.time()
        self.fillDestinations()
        rows = self.rows
        columns = self.columns
        v = rows*columns
        self.adjMatrix = AdjacencyMatrix(v)
        id = 0 ##Which Grid cell are we finding adjacents for
        for row in range(rows):
            for column in range(columns):
                self.adjMatrix.setCell(id, id, 0)
                self.adjMatrix.setPathCell(id, id, 0)
                ##Testing Cell to the left
                if column-1 >= 0:
                    adj_cell = self.grid[row][column-1]
                    if adj_cell.FILLED_COLOR != "black":
                        self.adjMatrix.setCell(id, adj_cell.id, 1)
                        self.adjMatrix.setPathCell(id, adj_cell.id, id)
                ##Testing Cell to the right
                if column+1 < columns:
                    adj_cell = self.grid[row][column+1]
                    if adj_cell.FILLED_COLOR != "black":
                        self.adjMatrix.setCell(id, adj_cell.id, 1)
                        self.adjMatrix.setPathCell(id, adj_cell.id, id)
                ##Testing Cell above
                if row-1 >= 0:
                    adj_cell = self.grid[row-1][column]
                    if adj_cell.FILLED_COLOR != "black":
                        self.adjMatrix.setCell(id, adj_cell.id, 1)
                        self.adjMatrix.setPathCell(id, adj_cell.id, id)
                ##Testing Cell below
                if row+1 < columns:
                    adj_cell = self.grid[row+1][column]
                    if adj_cell.FILLED_COLOR != "black":
                        self.adjMatrix.setCell(id, adj_cell.id, 1)
                        self.adjMatrix.setPathCell(id, adj_cell.id, id)
                id+=1
        time_end = time.time()
        print(time_end - time_start)

    def fwMatrix(self):
        print("Timing Floyd-Warshall")
        time_start = time.time()
        path = []
        rows = self.rows
        columns = self.columns

        v = rows*columns
        for k in range(v):
        # pick all edges as source one by one
            for i in range(v):
            # Pick all edges as destination for the
            # above picked source
                for j in range(v):
                # If edge k is on the shortest path from
                # i to j, then update the value of dist[i][j]
                    if (self.adjMatrix.getCell(i, k) + self.adjMatrix.getCell(k, j)) < self.adjMatrix.getCell(i, j):
                        self.adjMatrix.setCell(i, j, self.adjMatrix.getCell(i, k) + self.adjMatrix.getCell(k, j))
                        self.adjMatrix.setPathCell(i, j, self.adjMatrix.getPathCell(k, j))

        time_end = time.time()
        print(time_end - time_start)

    def tspFloydWarshall(self):
        print("Timing TSP on Floyd Warshall")
        time_start = time.time()
        fin_len = len(self.dest_cells) #the number of paths is equal to number of dest_cells
        finalpath = []
        alledges = []
        i = 0
        for cell in self.dest_cells:
            j=0
            for cell2 in self.dest_cells:
                if cell != cell2:
                    path = Edge(i, j, self.adjMatrix.getCell(cell2.id, cell.id))
                    alledges.append(path)
                j+=1
            i+=1
        alledges.sort(key = lambda x: x.distance) #we want to check paths greedily, i.e shortest ones get added first
        for edge in alledges: #removing duplicates
            for reverse in alledges:
                if edge.node1 == reverse.node2 and edge.node2 == reverse.node1:
                    alledges.remove(reverse)
                    break

        alledges_len = len(alledges)
        count_list = [0 for node in range(len(self.dest_cells))]
        for i in range(alledges_len):
            skippath = False
            curpath = alledges[i]
            start = curpath.node1
            dest = curpath.node2
            dist = curpath.distance
            if count_list[start] >= 2 or count_list[dest] >= 2:
                skippath = True

            else:
                graph = Graph(alledges_len+1)
                for edge in finalpath:
                    graph.addEdge(edge.node1, edge.node2)
                graph.addEdge(curpath.node1, curpath.node2)
                skippath = graph.isCyclic()


            if skippath is False:
                finalpath.append(curpath)
                count_list[start] += 1
                count_list[dest] += 1

            if len(finalpath) is fin_len-1:
                for i in range(len(count_list)):
                    if count_list[i] == 1:
                        count_list[i] += 1
                        start = i
                        break
                for j in range(i, len(count_list)):
                    if count_list[j] == 1:
                        count_list[j] += 1
                        end = j
                        break
                for edge in alledges:
                    if (edge.node1 == start and edge.node2 == end) or (edge.node2 == start and edge.node1 == end):
                        finalpath.append(edge)
                        break
                break
        total_dist = 0
        for edge in finalpath:
            id_start = self.dest_cells[edge.node1].id
            id_end = self.dest_cells[edge.node2].id
            draw_list = self.adjMatrix.pathList(id_start, id_end)
            for id in draw_list:
                x = id % self.columns
                y = (id - x)//self.rows
                self.makePathCell((x, y))
            total_dist += edge.distance
        self.finalPath = finalpath
        time_end = time.time()
        the_time = time_end-time_start
        print(time_end)
        print(time_start)
        print(the_time)
        print("Floyd Warshall Total Distance: ", total_dist)


    def allPathsAstar(self):
        print("Timing A* All Paths")
        time_start = time.time()
        self.fillDestinations()
        allpaths = [] #This will be a matrix of end nodes. There is an index in
            #allpaths for each node in self.dest_cells, with indices lining up
            #allpaths[] is a list of destination nodes. allpaths[][] is a specific
            #destination node
        i = 0
        for first_node in self.dest_cells: #starting Node
            pathlistlist = []
            j = 0
            for dest_node in self.dest_cells: #finds a path to every other node
                if first_node != dest_node: #don't find a path to yourself
                    (end_node, path, dist) = self.aStar(self.grid, (first_node.x, first_node.y), (dest_node.x, dest_node.y))
                    pathlistlist.append(end_node)
                    j+=1
            allpaths.append(pathlistlist) #append list
            i+=1
        self.astarpaths = allpaths
        time_end = time.time()
        print(time_end - time_start)

    def aStar(self, grid, start, end):

        def heuristic(a, b):
            (x1, y1) = a
            (x2, y2) = b
            return abs(x1 - x2) + abs(y1 - y2)


        def explore_adj(grid, node):
            rows = len(grid)
            columns = len(grid[0])
            (x, y) = node.position
            ##Adding Cell to the left as long is it is not black
            if x-1 >= 0:
                if grid[y][x-1].getColor() != "black":
                    node.addAdjacent(Node(node, (x-1, y)))
            ##Adding Cell to the right
            if x+1 < columns:
                if grid[y][x+1].getColor() != "black":
                    node.addAdjacent(Node(node, (x+1, y)))
            ##Adding Cell above
            if y-1 >= 0:
                if grid[y-1][x].getColor() != "black":
                    node.addAdjacent(Node(node, (x, y-1)))
            ##Adding Cell below
            if y+1 < columns:
                if grid[y+1][x].getColor() != "black":
                    node.addAdjacent(Node(node, (x, y+1)))

        start_node = Node(None, start)
        frontier = []
        heapq.heappush(frontier, (0, start_node))
        came_from = {}
        cost_so_far = {}
        came_from[start_node] = None
        cost_so_far[start_node] = 0
        neighbors = []
        end_node = None

        while len(frontier) != 0:
            (distance, current) = heapq.heappop(frontier)
            if current.position == end:
                end_node = current
                break

            neighbors = []
            explore_adj(grid, current)
            for neighbor in current.adjacents:
                neighbors.append(neighbor)

            for next in neighbors:
                new_cost = cost_so_far[current] + 1
                if next not in cost_so_far or new_cost < cost_so_far[next]:
                    cost_so_far[next] = new_cost
                    next.g = new_cost
                    priority = new_cost + heuristic(end, next.position)
                    heapq.heappush(frontier, (priority, next))
                    came_from[next] = current

        return end_node, came_from, cost_so_far

    def tspAStar(self):
        print("Timing TSP on A*")
        time_start = time.time()
        fin_len = len(self.dest_cells) #the number of paths is equal to number of dest_cells
        finalpath = []
        allpaths = []
        alledges = []
        i = 0
        for endNodeList in self.astarpaths:
            for node in endNodeList:
                path = (self.dest_cells[i], node, node.g)
                allpaths.append(path)
            i+=1
        allpaths.sort(key = lambda x: x[2]) #we want to check paths greedily, i.e shortest ones get added first
        for edge in allpaths: #removing duplicates
            (dest, node, dist) = edge
            for reverse in allpaths:
                (dest2, node2, dist2) = reverse
                if node.position == dest2.position and dest.position == node2.position:
                    allpaths.remove(reverse)
                    break
        for path in allpaths:
            i = 0
            (start, dest, dist) = path
            j = 0
            for k in self.dest_cells:
                if start.position == k.position:
                    break
                i+=1
            for k in self.dest_cells:
                if dest.position == k.position:
                    break
                j+=1
            alledges.append(Edge(i, j, dist))

        alledges_len = len(alledges)
        count_list = [0 for node in range(len(self.dest_cells))]
        for i in range(alledges_len):
            skippath = False
            curpath = alledges[i]
            start = curpath.node1
            dest = curpath.node2
            dist = curpath.distance
            if count_list[start] >= 2 or count_list[dest] >= 2:
                skippath = True

            else:
                graph = Graph(alledges_len+1)
                for edge in finalpath:
                    graph.addEdge(edge.node1, edge.node2)

                graph.addEdge(curpath.node1, curpath.node2)
                skippath = graph.isCyclic()


            if skippath is False:
                finalpath.append(curpath)
                count_list[start] += 1
                count_list[dest] += 1

            if len(finalpath) is fin_len-1:
                for i in range(len(count_list)):
                    if count_list[i] == 1:
                        count_list[i] += 1
                        start = i
                        break
                for j in range(i, len(count_list)):
                    if count_list[j] == 1:
                        count_list[j] += 1
                        end = j
                        break
                for edge in alledges:
                    if (edge.node1 == start and edge.node2 == end) or (edge.node2 == start and edge.node1 == end):
                        finalpath.append(edge)
                        break
                break

        total_dist = 0
        for edge in finalpath:
            i = 0
            for edge2 in alledges:
                if edge == edge2:
                    break
                i+=1
            (node1, node2, dist) = allpaths[i]
            temp = node2.parent
            while  temp is not None and temp.parent is not None:
                self.makePathCell(temp.position)
                temp = temp.parent
            total_dist += edge.distance
        self.finalPath = finalpath
        time_end = time.time()
        the_time = time_end-time_start
        print(the_time)
        print("A* Total Distance: ", total_dist)

if __name__ == "__main__" :
    app = Tk()

    grid = CellGrid(app, 20, 20, 15)
    grid.pack()

    menubar = Menu(app)
    filemenu = Menu(menubar, tearoff=0)
    filemenu.add_command(label="Save", command=grid.save)
    filemenu.add_separator()
    filemenu.add_command(label="Exit", command=app.quit)
    menubar.add_cascade(label="File", menu=filemenu)
    menubar.add_command(label="Pen", command=grid.onPen)
    menubar.add_command(label="Eraser", command=grid.onEraser)
    colormenu = Menu(menubar, tearoff=0)
    colormenu.add_command(label="Shelf", command=grid.makeShelfColor)
    colormenu.add_command(label="ListItem", command=grid.makeListItemColor)
    colormenu.add_command(label="Entrance", command=grid.makeEntranceColor)
    menubar.add_cascade(label="Color", menu=colormenu)
    makemenu = Menu(menubar, tearoff=0)
    makemenu.add_command(label="Matrix", command=grid.makeMatrix)
    menubar.add_cascade(label="Make Adjacency With", menu=makemenu)
    allpairsmenu = Menu(menubar, tearoff=0)
    allpairsmenu.add_command(label="Floyd-Warshall's Algorithm", command=grid.fwMatrix)
    allpairsmenu.add_command(label="A*", command=grid.allPathsAstar)
    menubar.add_cascade(label="Find all paths using", menu=allpairsmenu)
    searchmenu = Menu(menubar, tearoff=0)
    searchmenu.add_command(label="A*", command=grid.tspAStar)
    searchmenu.add_command(label="Floyd-Warshall", command=grid.tspFloydWarshall)
    menubar.add_cascade(label="Solve TSP From", menu=searchmenu)

    app.config(menu=menubar)

    app.mainloop()
