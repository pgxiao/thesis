# TODO: add, remove polyhedral
# 

if '' not in sys.path:
    sys.path = [''] + sys.path
from igp import *
from sage.numerical.mip import MIPSolverException
from sage.misc.all import cached_method
from collections import defaultdict
from itertools import product


###############################
# Polyhedral Arrangement
###############################

class PolyhedralArrangement(object):
    """
    Define a Polyhedral Arrangement.

    INPUT:

    - ``colletion`` -- either a list or a tuple of polyhedra, or a dictionary of polyhedra
      where the keys are the dimension of the polyhedra

    Attributes:

    - ``ambient_dim`` -- the ambient dim of each polyhedron
        
    - ``dim`` -- the maximal dimension among the polyhedra
        
    - ``size`` -- the numbers of polyhedra (not including sub-polyhedra)
      when set up the arrangement
    
    - ``grid`` -- a :class:`Grid` that can be used for discrete binary search
      on polyhedra
        
    - ``collection`` -- a dictionary of the polyhedra (not including sub-polyhedra)
      where the keys are the dimension of the polyhedra
        
    - ``grid_contents`` -- a dictionary of the ``grid``, the keys are buckets
      and the values are a set of polyhedra that intersect with the key
        
    - ``buckets`` -- a dictionary, the keys are polyhedra and the values are the
      buckets that intersect with the key (this attribute is like a dual
      of ``grid_contents``)

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
        self._grid = Grid(self._size, self._ambient_dim, width=None)
        self._collection = coll_dict
        self._grid_contents = self._grid._contents
        self._buckets = defaultdict(set)

    def __iter__(self):
        for polyhedron in self.collection_of_polyhedra():
            yield polyhedron

    def ambient_dimension(self):
        r"""
        The ambient dim of each polyhedron.
        """
        return self._ambient_dim

    def buckets(self):
        r"""
        A dictionary, the keys are polyhedra and the values are the
        buckets that intersect with the key (this attribute is like a dual
        of ``grid_contents``).
        """
        return self._buckets

    def collection_of_polyhedra(self):
        r"""
        A dictionary of the polyhedra (not including sub-polyhedra)
        where the keys are the dimension of the polyhedra.
        """
        c = set()
        coll_dict = self.collection_dict()
        for v in coll_dict.values():
            for p in v:
                c.add(p)
        return c

    def collection_dict(self):
        r"""
        A dictionary of the polyhedra (not including sub-polyhedra)
        where the keys are the dimension of the polyhedra.
        """
        return self._collection

    def dim(self):
        r"""
        The maximal dimension among the polyhedra.
        """
        return self._dim

    def grid(self):
        r"""
        A :class:``Grid`` that can be used for discrete binary search
        on polyhedra.
        """
        return self._grid

    def grid_contents(self):
        r"""
        A dictionary of the ``grid``, the keys are buckets and the
        values are a set of polyhedra that intersect with the key.
        """
        return self._grid_contents

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

        # QUESTION: what solver should I use
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
        # FIXME: (suggestion by Yuan) might use to_linear_program create LPs and inequalities
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

    def point_lookup(self, point):
        r"""
        Given a point, find where the bucket that the point belong to,
        and return the contents on that bucket as a set.

        EXAMPLES::

            sage: p = Polyhedron(vertices=[[8/21, 1/4], [4/5, 1/5], [5/6, 4/5]])
            sage: q = Polyhedron(vertices=[[1/2, 1/2], [5/6, 1/2], [1/2, 1]])
            sage: x = Polyhedron(vertices=[[4/5, 4/5]])
            sage: pa = PolyhedralArrangement([p, q, x])
            sage: pa.point_lookup(x)
            {A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices,
             A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices,
             A 0-dimensional polyhedron in QQ^2 defined as the convex hull of 1 vertex}
        """
        self.update_dictionaries()
        grid = self.grid()
        point = point.vertices_list()[0]
        bucket = grid.point_in_bucket(point)
        return self.grid_contents()[bucket]

    def size(self):
        r"""
        Return the size of the original collection of polyhedra.
        """
        return self._size

    @cached_method
    def update_dictionaries_for_a_polyhedron(self, p, selection=None):
        r"""
        Use binary search to find what buckets the polyhedron ``p``
        located in and update two dictionaries: ``grid_contents`` and
        ``buckets``.

        Recall:

        - ``grid_contents`` -- a dictionary of the ``grid``, the keys are buckets
          and the values are a set of polyhedra that intersect with the key
            
        - ``buckets`` -- a dictionary, the keys are polyhedra and the values are the
          buckets that intersect with the key (this attribute is like a dual
          of ``grid_contents``)

        INPUT:

        - ``p`` -- a :class:`Polyhedron`

        - ``selection`` -- (default: None) a tuple of two buckets
          (buckets are represented by its integer coordinates,
          see :class:`Grid` for examples)
          if ``selection`` is None, then choose the entire grid as
          selection

        EXAMPLES::

            sage: p = Polyhedron(vertices=[[8/21, 1/4], [4/5, 1/5], [5/6, 4/5]])
            sage: q = Polyhedron(vertices=[[1/2, 1/2], [4/5, 1/2], [1/2, 5/6]])
            sage: x = Polyhedron(vertices=[[4/5, 4/5]])
            sage: pa = PolyhedralArrangement([p, q, x])
            sage: pa.update_dictionaries_for_a_polyhedron(p)
            sage: pa.grid_contents()
            defaultdict(<type 'set'>, {(2, 0): set([A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices]), (1, 0): set([A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices]), (1, 1): set([A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices]), (2, 1): set([A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices]), (2, 2): set([A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices])})
            sage: pa.buckets()
            defaultdict(<type 'set'>, {A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices: set([(2, 0), (1, 0), (1, 1), (2, 1), (2, 2)])})
        """
        grid = self.grid()
        if selection is None:
            size = grid.size()
            dim = grid.dim()
            selection = (tuple(0 for i in range(dim)), tuple(size - 1 for i in range(dim)))
        lower_left = selection[0]
        upper_right = selection[1]
        if self.LP_intersect(grid.selection_to_polyhedron(lower_left, upper_right), p):
            if lower_left == upper_right:
                grid._contents[lower_left].add(p)
                self._buckets[p].add(lower_left)
            else:
                a, b = grid.cut_selection(lower_left, upper_right)
                self.update_dictionaries_for_a_polyhedron(p, a)
                self.update_dictionaries_for_a_polyhedron(p, b)

    @cached_method
    def update_dictionaries(self, selection=None):
        r"""
        For each polyhedron in the collection, use binary search to 
        find what buckets the polyhedron located in and update two
        dictionaries: ``bucket`` and ``grid_contents``.

        See :meth:`update_dictionaries_for_a_polyhedron` for more
        docstrings.

        EXAMPLES::

            sage: p = Polyhedron(vertices=[[8/21, 1/4], [4/5, 1/5], [5/6, 4/5]])
            sage: q = Polyhedron(vertices=[[1/2, 1/2], [5/6, 1/2], [1/2, 1]])
            sage: x = Polyhedron(vertices=[[4/5, 4/5]])
            sage: pa = PolyhedralArrangement([p, q, x])
            sage: pa.update_dictionaries()
            sage: pa.grid_contents()
            defaultdict(<type 'set'>, {(1, 2): set([A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices]), (2, 1): set([A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices, A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices]), (2, 0): set([A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices]), (2, 2): set([A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices, A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices, A 0-dimensional polyhedron in QQ^2 defined as the convex hull of 1 vertex]), (1, 0): set([A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices]), (1, 1): set([A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices, A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices])})
            sage: pa.buckets()
            defaultdict(<type 'set'>, {A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices: set([(2, 0), (1, 0), (1, 1), (2, 1), (2, 2)]), A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices: set([(1, 2), (1, 1), (2, 1), (2, 2)]), A 0-dimensional polyhedron in QQ^2 defined as the convex hull of 1 vertex: set([(2, 2)])})
        """
        for p in self.collection_of_polyhedra():
            self.update_dictionaries_for_a_polyhedron(p, selection)

class Grid(object):
    r"""
    Define a grid that are divided into buckets. The grid
    will be used for discrete binary search to find polyhedra
    intersection in :class:`PolyhedralArrangement`.

    # definition of terms:
    # 1. bucket - a single bucket in the grid with integer coordinates.
    # 2. selection - a bounch of buckets which can be determined by 
    #    the lower left bucket and upper right bucket.
    #    Think of a cube that can be determined by the lower left vertex
    #    and upper right vertex.

    INPUT:

    - ``number_of_poly`` -- an integer, the number of polyhedra
      in the colletion in a :class:`PolyhedralArrangement`

    - ``dim`` -- the dimension of the grid

    - ``width`` -- the width of the bucket

    Attributes:

    - ``width`` -- the width of each bucket

    - ``size`` -- an integer that indicates how many pieces
      are divided from 0 to 1

    - ``dim`` -- an integer that indicates the dimension
      of the grid

    - ``buckets`` -- a set that includes all the buckets
      in the grid

    - ``contents`` -- a dictionary, the keys are buckets
      and the values are the contents on the buckets. In
      this codes (so far), the contents are sets of polyhedra
      that intersect with the keys
    """ 
    def __init__(self, number_of_poly, dim, width=None):
        # size is the number of polyhedra
        # dim is the ambient dimension of the polyhedra
        # FIXME: width can only be fractional
        if width is None:
            # self._width = 1 / (sizre ^ (1 / dim))
            self._width = 1 / number_of_poly
        self._size = int(1 / self._width)
        self._dim = dim
        self._buckets = set(product(range(self._size), repeat=dim))
        self._contents = defaultdict(set)

    def buckets(self):
        r"""
        Return a set that includes all the buckets in the grid


        EXAMPLES::

            sage: g = Grid(3, 2)
            sage: g.buckets()
            {(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)}
        """
        return self._buckets

    def bucket_to_hypercube(self, lower_left):
        r"""
        Return a hypercube in standard width by giving the coordinates
        of the lower left bucket.

        EXAMPLES::

            sage: g = Grid(3, 3)
            sage: g.bucket_to_hypercube((0, 0, 0)).vertices()
            (A vertex at (0, 0, 0),
             A vertex at (0, 0, 1/3),
             A vertex at (0, 1/3, 0),
             A vertex at (0, 1/3, 1/3),
             A vertex at (1/3, 0, 0),
             A vertex at (1/3, 0, 1/3),
             A vertex at (1/3, 1/3, 0),
             A vertex at (1/3, 1/3, 1/3))
        """
        origin = self.get_coordinate(lower_left)
        unit_grid_iter = product([0, self.width()], repeat=self.dim())
        unit_grid = [list(v) for v in unit_grid_iter]
        v_list = [0] * len(unit_grid)
        for index, v in enumerate(unit_grid):
            v_list[index] = [o + p for o, p in zip(v, origin)]
        return Polyhedron(vertices=v_list)

    def change_coordinate(self, bucket, index, change):
        r"""
        Change one coordinate of the given bucket.

        EXAMPLES::

            sage: g = Grid(3, 3)
            sage: g.change_coordinate((0, 1, 2), 2, -1)
            (0, 1, 1)
        """
        return bucket[:index] + (bucket[index] + change,) + bucket[1 + index:]

    def contents(self):
        r"""
        A dictionary, the keys are buckets and the values are the contents
        on the buckets. In this codes (so far), the contents are sets of
        polyhedra that intersect with the keys.
        """
        return self._contents

    def cut_selection(self, lower_left, upper_right):
        r"""
        Given the lower left bucket and upper right bucket of the selection,
        find the 'longest' edges, and cut it into two new selections.

        If all edges are equal, cut the selection from its first coordinate.

        Return two selections with their lower left and upper right buckets.

        EXAMPLES::

            sage: g = Grid(3, 3)
            sage: g.cut_selection((0, 0, 0), (2, 2, 2))
            (((0, 0, 0), (0, 2, 2)), ((1, 0, 0), (2, 2, 2)))
            sage: g.cut_selection((1, 1, 1), (1, 1, 1))
            ((1, 1, 1), (1, 1, 1))
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
        # cut the selection into two new selection
        # assume the lower left selection is smaller if length is odd
        small = (lower_left, self.change_coordinate(upper_right, index, -upper_change))
        large = (self.change_coordinate(lower_left, index, change), upper_right)
        return small, large

    def dim(self):
        r"""
        Return the dimension of the grid.
        """
        return self._dim

    def edges_of_selection(self, lower_left, upper_right):
        r"""
        Return the lengths of the edges of the selection.

        EXAMPLES::

            sage: g = Grid(3, 3)
            sage: g.edges_of_selection((0, 1, 1), (1, 2, 1))
            [1, 1, 0]
        """
        return [c1 - c0 for c0, c1 in zip(lower_left, upper_right)]

    def get_coordinate(self, bucket):
        r"""
        Get the actual coordinate of the bucket.

        EXAMPLES::

            sage: g = Grid(3, 3)
            sage: g.get_coordinate((0, 1, 2))
            (0, 1/3, 2/3)
        """
        return tuple(coord * self.width() for coord in bucket)

    def longest_edge(self, lower_left, upper_right):
        r"""
        Find the longest edge of a selection.

        EXAMPLES::

            sage: g = Grid(3, 3)
            sage: g.longest_edge((0, 1, 1), (1, 2, 1))
            (0, 1)
        """
        edges = self.edges_of_selection(lower_left, upper_right)
        m = max(edges)
        index = edges.index(m)
        return index, m

    def selection_to_polyhedron(self, lower_left, upper_right):
        r'''
        Convert a selection to a polyhedron.

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
        r"""
        Return a bucket where the point are located in.

        EXAMPLES:

            sage: g = Grid(3, 3)
            sage: g.point_in_bucket((1/4, 1/2, 1))
            (0, 1, 2)
        """
        return tuple(((p) // (self._width)).floor() if p != 1
                    else self._size - 1
                    for p in point)

    def width(self):
        r"""
        Return the width of the grid.

        EXAMPLES::

            sage: g = Grid(2, 3)
            sage: g.width()
            1/2
        """
        return self._width

    def size(self):
        r"""
        Return the size of the grid.

        EXAMPLES::

            sage: g = Grid(2, 3)
            sage: g.size()
            2
        """
        return self._size






