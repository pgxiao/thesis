# FIXME: search, iteration should be equal to k dim times, not just 1
# TODO: add, remove polyhedral
# TODO: buckets search

if '' not in sys.path:
    sys.path = [''] + sys.path
from igp import *
from sage.numerical.mip import MIPSolverException

import itertools

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
        self._size = sum([len(v) for v in coll_dict.values()])
        self._grid = Grid(self._size, self._ambient_dim)
        self._coll_dict = coll_dict
        self._intersect_dict = {}

    def ambient_dimension(self):
        return self._ambient_dim

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
        return self.grid().grid_dict()

    def intersect_dict(self):
        return self._intersect_dict

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

    def search_polyhedron(self, p, area=None, limit=None):
        r"""
        Search what buckets the polyhedron ``p`` located in
        and update the bucket dictionary.

        EXAMPLES::

            sage: p = Polyhedron(vertices=((1/4, 1/2), (1/2, 1/2), (1/4, 3/4), (1/2, 3/4)))
            sage: PA = PolyhedralArrangement((p,))
            sage: PA.search_polyhedron(p, limit=1/4)
            sage: d = PA.grid_dict()
            sage: d.keys()
            [((0, 3/4), (0, 1), (1/4, 3/4), (1/4, 1)),
             ((1/2, 1/4), (1/2, 1/2), (3/4, 1/4), (3/4, 1/2)),
             ((0, 1/2), (0, 3/4), (1/4, 1/2), (1/4, 3/4)),
             ((1/2, 3/4), (1/2, 1), (3/4, 3/4), (3/4, 1)),
             ((1/4, 1/4), (1/4, 1/2), (1/2, 1/4), (1/2, 1/2)),
             ((1/4, 3/4), (1/4, 1), (1/2, 3/4), (1/2, 1)),
             ((1/2, 1/2), (1/2, 3/4), (3/4, 1/2), (3/4, 3/4)),
             ((1/4, 1/2), (1/4, 3/4), (1/2, 1/2), (1/2, 3/4)),
             ((0, 1/4), (0, 1/2), (1/4, 1/4), (1/4, 1/2))]
        """
        # FIXME: need tests in k-dim
        def hash_area(area):
            return tuple(map(tuple, area))
        grid = self.grid()
        if area is None:
            area = self.grid().standard_grid()
            area_polyhedron = self.grid().standard_grid_polyhedron()
        else:
            area_polyhedron = Polyhedron(vertices=area)
        if limit is None:
            limit = self.grid().width()

        if self.LP_intersect(area_polyhedron, p):
            edges = grid.lengths_of_edges(area)
            if all(e <= limit for e in edges):
                key = hash_area(area)
                if key in grid._dict:
                    grid._dict[key].add(p)
                else:
                    grid._dict[key] = set([p])
                if p in self._intersect_dict:
                    self._intersect_dict[p].add(key)
                else:
                    self._intersect_dict[p] = set()
                    self._intersect_dict[p].add(key)
            else:
                a, b = grid.cut_grid(area)
                self.search_polyhedron(p, a, limit)
                self.search_polyhedron(p, b, limit)

    def search(self, area=None, limit=None):
        r"""
        For each polyhedron in the collection, search which grid does
        the polyhedron located in and update the grid dictionary.
        """
        for p in self.collection():
            self.search_polyhedron(p, area, limit)

class Grid:
        """docstring for Grid"""
        def __init__(self, size, dim):
            # size is the number of polyhedra
            # dim is the ambient dimension of the polyhedra
            self._size = size
            self._dim = dim
            self._width = 1 / (size ^ (1 / dim))
            self._dict = {}

        def build_grid(self, low_pt, width=None):
            r"""
            Build a single grid by given the lowest point of grid
            Return the vertices of the grid

            EXAMPLES::

                sage: g = Grid(2, 3)
                sage: g.build_grid([0, 0, 0], 1)
                [[0, 0, 0],
                 [0, 0, 1],
                 [0, 1, 0],
                 [0, 1, 1],
                 [1, 0, 0],
                 [1, 0, 1],
                 [1, 1, 0],
                 [1, 1, 1]]
            """
            if width is None:
                width = self.width()
            unit_grid_iterator = itertools.product([0, width], repeat=self.dimension())
            unit_grid = [list(v) for v in unit_grid_iterator]
            v_list = [0] * len(unit_grid)
            for index, v in enumerate(unit_grid):
                v_list[index] = [o + p for o, p in zip(v, low_pt)]
            return v_list

        def build_grid_polyhedron(self, low_pt, width=None):
            r"""
            Build a single grid as a Polyhedron by given the lowest point of grid
            Return the vertices of the grid

            EXAMPLES::

                sage: g = Grid(2, 3)
                sage: p = g.build_grid_polyhedron([0, 0, 0], 1)
                sage: p.vertices()
                (A vertex at (0, 0, 0),
                 A vertex at (0, 0, 1),
                 A vertex at (0, 1, 0),
                 A vertex at (0, 1, 1),
                 A vertex at (1, 0, 0),
                 A vertex at (1, 0, 1),
                 A vertex at (1, 1, 0),
                 A vertex at (1, 1, 1))
            """
            if width is None:
                width = self.width()
            return Polyhedron(vertices=self.build_grid(low_pt, width))

        def cut_grid(self, area):
            r"""
            Given the vertices of the area, find the 'longest' part, and cut
            it into two equal parts.

            EXAMPLES::

                sage: g = Grid(2, 3)
                sage: v2 = [[2, 3, 4],
                ....:  [2, 3, 9],
                ....:  [2, 10, 4],
                ....:  [2, 10, 9],
                ....:  [8, 3, 4],
                ....:  [8, 3, 9],
                ....:  [8, 10, 4],
                ....:  [8, 10, 9]]
                sage: x, y = g.cut_grid(v2)
                sage: x
                [[2, 3, 4],
                 [2, 3, 9],
                 [2, 13/2, 4],
                 [2, 13/2, 9],
                 [8, 3, 4],
                 [8, 3, 9],
                 [8, 13/2, 4],
                 [8, 13/2, 9]]
                sage: y
                [[2, 13/2, 4],
                 [2, 13/2, 9],
                 [2, 10, 4],
                 [2, 10, 9],
                 [8, 13/2, 4],
                 [8, 13/2, 9],
                 [8, 10, 4],
                 [8, 10, 9]]
            """
            index, length = self.longest_edge(area)
            a = deepcopy(area)
            b = deepcopy(area)
            lower = area[0][index]
            high = area[-1][index]
            change = (high - lower) / 2
            for i, v in enumerate(area):
                if v[index] == high:
                    a[i][index] = lower + change
                else:
                    b[i][index] = lower + change
            return a, b

        def dimension(self):
            return self._dim

        def grid_dict(self):
            return self._dict

        def lengths_of_edges(self, polytope):
            r"""
            Return a list of the lengths of a group of edges

            EXAMPLES::

                sage: g = Grid(2, 3)
                sage: v1 = g.build_grid([2, 3, 4], 1)
                sage: g.lengths_of_edges(v1)
                [1, 1, 1]
                sage: v2 = [[2, 3, 4],
                ....:  [2, 3, 9],
                ....:  [2, 10, 4],
                ....:  [2, 10, 9],
                ....:  [8, 3, 4],
                ....:  [8, 3, 9],
                ....:  [8, 10, 4],
                ....:  [8, 10, 9]]
                sage: g.lengths_of_edges(v2)
                [6, 7, 5]
            """
            dim = self.dimension()
            lengths = [0] * dim
            # this part look weird, but it works. The trick is to know how
            # itertools.product construct the list in build_grid(self, low_pt)
            for i in range(0, dim):
                lengths[dim-i-1] = polytope[2^i][dim-i-1] - polytope[0][dim-i-1]
            return lengths

        def longest_edge(self, polytope):
            r"""
            Find the longest edge of the polytope and return its index and the length
            of the longest edge.

            EXAMPLES::

                sage: g = Grid(1, 4)
                sage: v1 = g.build_grid([0, 0, 0, 0], 1)
                sage: x, y = g.cut_grid(v1)
                sage: x
                [[0, 0, 0, 0],
                 [0, 0, 0, 1],
                 [0, 0, 1, 0],
                 [0, 0, 1, 1],
                 [0, 1, 0, 0],
                 [0, 1, 0, 1],
                 [0, 1, 1, 0],
                 [0, 1, 1, 1],
                 [1/2, 0, 0, 0],
                 [1/2, 0, 0, 1],
                 [1/2, 0, 1, 0],
                 [1/2, 0, 1, 1],
                 [1/2, 1, 0, 0],
                 [1/2, 1, 0, 1],
                 [1/2, 1, 1, 0],
                 [1/2, 1, 1, 1]]
                sage: y
                [[1/2, 0, 0, 0],
                 [1/2, 0, 0, 1],
                 [1/2, 0, 1, 0],
                 [1/2, 0, 1, 1],
                 [1/2, 1, 0, 0],
                 [1/2, 1, 0, 1],
                 [1/2, 1, 1, 0],
                 [1/2, 1, 1, 1],
                 [1, 0, 0, 0],
                 [1, 0, 0, 1],
                 [1, 0, 1, 0],
                 [1, 0, 1, 1],
                 [1, 1, 0, 0],
                 [1, 1, 0, 1],
                 [1, 1, 1, 0],
                 [1, 1, 1, 1]]
                sage: g = Grid(2, 3)
                sage: v1 = g.build_grid([2, 3, 4], 1)
                sage: g.longest_edge(v1)
                (0, 1)
                sage: v2 = [[2, 3, 4],
                ....:  [2, 3, 9],
                ....:  [2, 10, 4],
                ....:  [2, 10, 9],
                ....:  [8, 3, 4],
                ....:  [8, 3, 9],
                ....:  [8, 10, 4],
                ....:  [8, 10, 9]]
                sage: g.longest_edge(v2)
                (1, 7)
            """
            lengths = self.lengths_of_edges(polytope)
            m = max(lengths)
            index = lengths.index(m)
            return index, m

        def width(self):
            return self._width

        def size(self):
            return self._size

        def standard_grid(self):
            r"""
            Return the vertices representation of the standard grid
            which is a hypercube with the origin at 0 and each edge
            has length 1

            EXAMPLES::

                sage: g = Grid(2, 3)
                sage: g.standard_grid()
                [[0, 0, 0],
                 [0, 0, 1],
                 [0, 1, 0],
                 [0, 1, 1],
                 [1, 0, 0],
                 [1, 0, 1],
                 [1, 1, 0],
                 [1, 1, 1]]
            """
            origin = [0 for i in range(self.dimension())]
            return self.build_grid(origin, 1)

        def standard_grid_polyhedron(self):
            r"""
            Return the standard grid which is a hypercube with
            the origin at 0 and each edge has length 1

            EXAMPLES::

                sage: g = Grid(1, 3)
                sage: p = g.standard_grid_polyhedron()
                sage: p.vertices()
                (A vertex at (0, 0, 0),
                 A vertex at (0, 0, 1),
                 A vertex at (0, 1, 0),
                 A vertex at (0, 1, 1),
                 A vertex at (1, 0, 0),
                 A vertex at (1, 0, 1),
                 A vertex at (1, 1, 0),
                 A vertex at (1, 1, 1))
            """
            return Polyhedron(vertices=self.standard_grid())






