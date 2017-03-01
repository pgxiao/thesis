# FIXME: search, iteration should be equal to k dim times, not just 1
# TODO: add, remove polyhedral
# TODO: buckets search

if '' not in sys.path:
    sys.path = [''] + sys.path
from igp import *
from sage.numerical.mip import MIPSolverException
from collections import defaultdict
from itertools import product


###############################
# Polyhedral Arrangement
###############################

class PolyhedralArrangement:
    """
    Define a Polyhedral Arrangement.

    EXAMPLES::

        sage: p = Polyhedron(ieqs = [[0,1,0,0,0],[0,0,1,0,0],[0,0,0,1,0],[0,0,0,0,1]], eqns = [[1,-1,-1,-1,-1]])
        sage: q = Polyhedron(eqns = [[10,30,50,60,70]])
        sage: collection = (p, q)
        sage: PA = PolyhedralArrangement(collection)
    """
    def __init__(self, colletion):
        if isinstance(colletion, (list, tuple)):
            coll_dict = {}
            for p in colletion:
                d = p.dim()
                if d in coll_dict:
                    coll_dict[d].append(p)
                else:
                    coll_dict[d] = [p]
        elif isinstance(colletion, dict):
            coll_dict = copy(colletion)
        else:
            raise ValueError
        if not coll_dict:
            return
        self._ambient_dim = coll_dict.values()[0][0].ambient_dim()
        self._dim = max(coll_dict.keys())
        # size is the numbers of polyhedra (not including sub-polyhedra) when set up the arrangement
        self._size = sum([len(v) for v in coll_dict.values()])
        self._coll_dict = coll_dict
        self._grid = Grid(self._size, self._ambient_dim, width=None)
        self._buckets = defaultdict(set)

    def ambient_dimension(self):
        return self._ambient_dim

    def buckets(self):
        return self._buckets

    def collection(self):
        r"""
        Return a set of polyhedra in the collection
        (only include the maximal ones)
        """
        c = set()
        coll_dict = self.collection_dict()
        for v in coll_dict.values():
            for p in v:
                c.add(p)
        return c

    def collection_dict(self):
        return self._coll_dict

    def dim(self):
        r"""
        Return highest dimension of the polyhedra
        """
        return self._dim

    def grid(self):
        return self._grid

    def grid_dict(self):
        return self.grid().dict()

    def LP_for_intersection(self, p, q):
        r"""
        Construct a LP to solve if polyhedron ``p`` and polyhedron ``q`` intersect

        EXAMPLES::

            sage: p = Polyhedron(ieqs = [[0,1,0,0,0],[0,0,1,0,0],[0,0,0,1,0],[0,0,0,0,1]], eqns = [[1,-1,-1,-1,-1]])
            sage: q = Polyhedron(eqns = [[10,30,50,60,70]])
            sage: PA = PolyhedralArrangement((p, q))
            sage: lp = PA.LP_for_intersection(p, q)
            sage: lp.show()
            Maximization:
            <BLANKLINE>
            <BLANKLINE>
            Constraints:
              1.0 <= x_0 + x_1 + x_2 + x_3 <= 1.0
              -1.0 <= 3.0 x_0 + 5.0 x_1 + 6.0 x_2 + 7.0 x_3 <= -1.0
              - x_0 <= 0.0
              x_0 + x_1 + x_2 <= 1.0
              - x_2 <= 0.0
              - x_1 <= 0.0
            Variables:
              x_0 is a continuous variable (min=-oo, max=+oo)
              x_1 is a continuous variable (min=-oo, max=+oo)
              x_2 is a continuous variable (min=-oo, max=+oo)
              x_3 is a continuous variable (min=-oo, max=+oo)
            sage: # compare with the equations and inequalities from the polyhedra
            sage: p.equations(); q.equations(); p.inequalities(); q.inequalities()
            (An equation (1, 1, 1, 1) x - 1 == 0,)
            (An equation (3, 5, 6, 7) x + 1 == 0,)
            (An inequality (1, 0, 0, 0) x + 0 >= 0,
             An inequality (-1, -1, -1, 0) x + 1 >= 0,
             An inequality (0, 0, 1, 0) x + 0 >= 0,
             An inequality (0, 1, 0, 0) x + 0 >= 0)
            ()
        """
        if dim(p) == -1 or dim(q) == -1:
            raise ValueError("Cannot intersect with empty polyhedron")

        lp = MixedIntegerLinearProgram(solver='GLPK')
        x = lp.new_variable()
        lp.set_objective(0)

        def linear_constraint(cstr, cstr_type):
            """
            Construct linear constraint (can be equation or inequality depends
            on constraint type 'cstr_type') by the given constraint 'cstr'
            """
            s = sum(x[index] * coef for index, coef in enumerate(cstr[1:]))
            if cstr_type == "==":
                return s == -cstr[0]
            else:
                return s >= -cstr[0]

        eqns = p.equations_list() + q.equations_list()
        ieqs = p.inequalities_list() + q.inequalities_list()
        for eqn in eqns:
            f = linear_constraint(eqn, "==")
            lp.add_constraint(f)
        for ieq in ieqs:
            g = linear_constraint(ieq, ">=")
            lp.add_constraint(g)
        return lp

    def LP_intersect(self, p, q):
        r"""
        Use LP to check if two polyhedra intersect.
        Return True if polyhedron ``p`` and polyhedron ``q`` intersect.
        Return False it they do not intersect.

        EXAMPLES::

            sage: p = Polyhedron(ieqs = [[0,1,0,0,0],[0,0,1,0,0],[0,0,0,1,0],[0,0,0,0,1]], eqns = [[1,-1,-1,-1,-1]])
            sage: q = Polyhedron(eqns = [[10,30,50,60,70]])
            sage: PA = PolyhedralArrangement((p, q))
            sage: PA.LP_intersect(p, q)
            False
            sage: p.intersection(q)
            The empty polyhedron in QQ^4

            sage: cube = polytopes.hypercube(3)
            sage: oct = polytopes.cross_polytope(3)
            sage: PA.LP_intersect(cube, oct)
            True
            sage: cube.intersection(oct*2)
            A 3-dimensional polyhedron in ZZ^3 defined as the convex hull of 12 vertices

            sage: P = Polyhedron([(0,0),(1,1)], base_ring=ZZ)
            sage: PA.LP_intersect(P, P)
            True
            sage: P.intersection(P)
            A 1-dimensional polyhedron in ZZ^2 defined as the convex hull of 2 vertices

            sage: Q = Polyhedron([(0,1),(1,0)], base_ring=ZZ)
            sage: PA.LP_intersect(P, P)
            True
        """
        lp = self.LP_for_intersection(p, q)
        try:
            lp.solve()
            return True
        except MIPSolverException:
            return False
        else:
            print "Unexpected error"
            raise

    def size(self):
        r"""
        Return the size of the original collection of polyhedra
        """
        return self._size

    def search_polyhedron(self, p, selection=None):
        r"""
        Search what buckets the polyhedron ``p`` located in
        and update the bucket dictionary.
        """
        grid = self.grid()
        if selection is None:
            size = grid.size()
            dim = grid.dim()
            selection = (tuple(0 for i in range(dim)), tuple(size - 1 for i in range(dim)))
        print "searching selection", selection
        lower_left = selection[0]
        upper_right = selection[1]
        if self.LP_intersect(grid.selection_to_polyhedron(lower_left, upper_right), p):
            print "intersect"
            print "lower_left", lower_left
            print "upper_right", upper_right
            if lower_left == upper_right:
                grid._contents[lower_left].add(p)
                self._buckets[p].add(lower_left)
            else:
                print "lower_left != upper_right"
                a, b = grid.cut_selection(lower_left, upper_right)
                self.search_polyhedron(p, a)
                self.search_polyhedron(p, b)

    def search(self, selection=None):
        r"""
        For each polyhedron in the collection, search which grid does
        the polyhedron located in and update the grid dictionary.
        """
        for p in self.collection():
            self.search_polyhedron(p, selection)

class Grid:
        """docstring for Grid"""
        def __init__(self, number_of_poly, dim, width=None):
            # size is the number of polyhedra
            # dim is the ambient dimension of the polyhedra
            # FIXME: width can only be fractional
            if width is None:
                # self._width = 1 / (size ^ (1 / dim))
                self._width = 1 / number_of_poly
                # FIXME: check width types, raise error if not fractional
            self._size = int(1 / self._width)
            self._dim = dim
            self._coord = [i * self._width for i in range(0, 1 + self._size)]
            self._buckets = set(product(range(self._size), repeat=dim))
            self._contents = defaultdict(set)

        # definition of terms:
        # 1. bucket - a single bucket in the grid with integer coordinates.
        # 2. selection - a bounch of buckets which can be determined by 
        #    the lower left bucket and upper right bucket.
        #    Think of a cube that can be determined by the lower left vertex
        #    and upper right vertex.

        def buckets(self):
            return self._buckets

        def bucket_to_hypercube(self, lower_left):
            r"""
            Return a hypercube with standard width by giving the actual coordinates
            of the lower left vertex of hypercube.
            """
            origin = self.get_coordinate(lower_left)
            unit_grid_iter = product([0, self.width()], repeat=self.dim())
            unit_grid = [list(v) for v in unit_grid_iter]
            v_list = [0] * len(unit_grid)
            for index, v in enumerate(unit_grid):
                v_list[index] = [o + p for o, p in zip(v, origin)]
            return Polyhedron(vertices=v_list)

        def change_coordinate(self, bucket, index, change):
            # change one coordinate of the given bucket
            return bucket[:index] + (bucket[index] + change,) + bucket[1 + index:]

        def cut_selection(self, lower_left, upper_right):
            r"""
            Given the lower left vertice and upper right vertice of the selection,
            find the 'longest' part, and cut it into two equal parts.

            Return two tuples of the lower left and upper right vertices
            of the two buckets.
            """
            if lower_left == upper_right:
                return lower_left, lower_left
            index, length = self.longest_edge(lower_left, upper_right)
            change = (length + 1) // 2
            if length % 2 == 0:
                # odd number of buckets
                upper_change = change + 1
            else:
                upper_change = change
            # cut the bucket into two buckets
            # assume the lower one is smaller if length is odd
            small = (lower_left, self.change_coordinate(upper_right, index, -upper_change))
            large = (self.change_coordinate(lower_left, index, change), upper_right)
            return small, large

        def dim(self):
            return self._dim

        def dict(self):
            return self._contents

        def edges_of_selection(self, lower_left, upper_right):
            return [c1 - c0 for c0, c1 in zip(lower_left, upper_right)]

        def get_coordinate(self, bucket):
            # get the actual coordinate of the bucket
            return tuple(coord * self.width() for coord in bucket)

        def longest_edge(self, lower_left, upper_right):
            edges = self.edges_of_selection(lower_left, upper_right)
            m = max(edges)
            index = edges.index(m)
            return index, m

        def selection_to_polyhedron(self, lower_left, upper_right):
            r'''
            EXAMPLES::

                sage: g = Grid(3, 3)
                sage: # build a flat box 
                sage: # (i.e. the height is half of the width or of the length)
                sage: p = g.selection_to_polyhedron((1, 1, 2), (2, 2, 2))
                sage: p.vertices()
                (A vertex at (1, 1, 1),
                 A vertex at (1/3, 1/3, 2/3),
                 A vertex at (1/3, 1/3, 1),
                 A vertex at (1/3, 1, 2/3),
                 A vertex at (1/3, 1, 1),
                 A vertex at (1, 1/3, 2/3),
                 A vertex at (1, 1/3, 1),
                 A vertex at (1, 1, 2/3))
            '''
            if lower_left == upper_right:
                return self.bucket_to_hypercube(lower_left)
            edges = self.edges_of_selection(lower_left, upper_right)
            # note: upper_right is the bucket that is hased with
            # the actual lower left vertex of the bucket
            # therefore, to get the actual upper right vertex of the selection
            # all coordinates of the upper right bucket needed to add one
            new_upper_right = tuple(c + 1 for c in upper_right)
            v = set([lower_left, new_upper_right])
            for i in range(self.dim()):
                up = self.change_coordinate(lower_left, i, edges[i]+1)
                down = self.change_coordinate(new_upper_right, i, -edges[i]-1)
                v.add(up)
                v.add(down)
            vertices = [self.get_coordinate(p) for p in list(v)]
            return Polyhedron(vertices=vertices)
 
        def point_in_bucket(self, point):

            return tuple(((p) // (self._width)).floor() if p != 1
                        else self._size - 1
                        for p in point)

        def width(self):
            return self._width

        def size(self):
            return self._size






